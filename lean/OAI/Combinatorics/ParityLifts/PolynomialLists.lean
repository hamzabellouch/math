import OAI.Combinatorics.ParityLifts.Polynomial

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.map {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → β} (P : PolyProgram α β f) :
    PolyProgram (List α) (List β) (List.map f) := by
  let stepP := ((PolyProgram.fst α (List β)).comp P).pair (PolyProgram.snd α (List β)) |>.comp
    (PolyProgram.cons β)
  have hg (a : α) (bs : List β) :
      (treeEncode (f a :: bs)).size ≤ (treeEncode bs).size +
        (P.coefficient + 1) * ((treeEncode a).size + 1) ^ (P.degree + 1) := by
    have hs := (P.program.run a).bounds.2.1
    have ht := P.bound a
    have hm : ((treeEncode a).size + 1) ^ P.degree ≤
        ((treeEncode a).size + 1) ^ (P.degree + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm' := Nat.mul_le_mul_left P.coefficient hm
    have hp : 1 ≤ ((treeEncode a).size + 1) ^ (P.degree + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [treeEncode_cons, DataTree.size]
    nlinarith
  let F := stepP.foldlGrowing (P.coefficient + 1) (P.degree + 1) hg
  let init := (PolyProgram.id (List α)).pair (PolyProgram.const ([] : List β))
  refine (init.comp F |>.comp (PolyProgram.reverse β)).congr ?_
  intro xs
  change (xs.foldl (fun bs a => f a :: bs) []).reverse = xs.map f
  have he (xs : List α) (bs : List β) :
      xs.foldl (fun ys a => f a :: ys) bs = (xs.map f).reverse ++ bs := by
    induction xs generalizing bs with
    | nil => simp
    | cons a xs ih => simp [ih, List.append_assoc]
  simp [he]

def PolyProgram.filter {α : Type} [TreeCodec α]
    {f : α → Bool} (P : PolyProgram α Bool f) :
    PolyProgram (List α) (List α) (List.filter f) := by
  let stepP := ((PolyProgram.fst α (List α)).comp P).ite
    (PolyProgram.cons α) (PolyProgram.snd α (List α))
  have hg (a : α) (bs : List α) :
      (treeEncode (if f a then a :: bs else bs)).size ≤
        (treeEncode bs).size + 1 * ((treeEncode a).size + 1) ^ 1 := by
    cases f a <;> simp only [Bool.false_eq_true, ↓reduceIte, treeEncode_cons, DataTree.size, Nat.one_mul, pow_one] <;> omega
  let F := stepP.foldlGrowing 1 1 hg
  refine (((PolyProgram.id (List α)).pair (PolyProgram.const ([] : List α))).comp F |>.comp
    (PolyProgram.reverse α)).congr ?_
  intro xs
  change (xs.foldl (fun bs a => if f a then a :: bs else bs) []).reverse = xs.filter f
  have he (xs : List α) (bs : List α) :
      xs.foldl (fun ys a => if f a then a :: ys else ys) bs = (xs.filter f).reverse ++ bs := by
    induction xs generalizing bs with
    | nil => simp
    | cons a xs ih => cases h : f a <;> simp [h, ih, List.append_assoc]
  simp [he]

def PolyProgram.flatten (α : Type) [TreeCodec α] :
    PolyProgram (List (List α)) (List α) List.flatten := by
  let stepP := PolyProgram.append α
  have hg (a b : List α) : (treeEncode (a ++ b)).size ≤
      (treeEncode b).size + 1 * ((treeEncode a).size + 1) ^ 1 := by
    have := treeEncode_append_size a b
    simp only [Nat.one_mul, pow_one]
    omega
  let F := stepP.foldlGrowing 1 1 hg
  let init := ((PolyProgram.reverse (List α)).pair (PolyProgram.const ([] : List α)))
  refine (init.comp F).congr ?_
  intro xs
  change xs.reverse.foldl (fun bs a => a ++ bs) [] = xs.flatten
  rw [List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma TreeProgram.foldWork_prefix {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : TreeProgram (α × β) β f) (xs : List α) (b : β) (S B : ℕ)
    (hs : ∀ ys zs, ys ++ zs = xs →
      (treeEncode (zs, ys.foldl (fun c a => f (a, c)) b)).size ≤ S)
    (hb : ∀ ys a zs, ys ++ a :: zs = xs →
      P.time (a, ys.foldl (fun c a => f (a, c)) b) ≤ B) :
    P.foldWork xs b ≤ (xs.length + 1) * (10 * (S + 1) + B + 1) := by
  induction xs generalizing b with
  | nil =>
    have h := hs [] [] rfl
    simpa only [foldWork, List.nil_append, List.foldl_nil] using h.trans
      (show S ≤ (List.length ([] : List α) + 1) * (10 * (S + 1) + B + 1) by simp; omega)
  | cons a xs ih =>
    have h := hs [] (a :: xs) rfl
    have hb₀ := hb [] a xs rfl
    have ht := ih (f (a, b))
      (fun ys zs he => by
        simpa using hs (a :: ys) zs (by simpa using congrArg (List.cons a) he))
      (fun ys c zs he => by
        simpa using hb (a :: ys) c zs (by simpa using congrArg (List.cons a) he))
    simp only [List.foldl_nil] at h hb₀
    simp only [foldWork, List.length_cons]
    nlinarith

def PolyProgram.foldlBounded {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (A e : ℕ)
    (hg : ∀ (xs : List α) (b : β), (treeEncode (xs.foldl (fun c a => f (a, c)) b)).size ≤
      A * ((treeEncode (xs, b)).size + 1) ^ e) :
    PolyProgram (List α × β) β (fun x => x.1.foldl (fun b a => f (a, b)) x.2) where
  program := P.program.foldl
  coefficient := 2 * (10 * (A + 3) + P.coefficient * (A + 3) ^ P.degree + 1) + 1
  degree := (e + 1) + (e + 1) * P.degree + 1
  bound := by
    rintro ⟨xs, b⟩
    let X := (treeEncode (xs, b)).size + 1
    let R := A * X ^ e
    let S := (treeEncode xs).size + R + 1
    let m := e + 1
    let d := P.degree
    let H := A + 3
    let K := 10 * H + P.coefficient * H ^ d + 1
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hxL : (treeEncode xs).size ≤ X := by simp [X, DataTree.size]; omega
    have hlen : xs.length + 1 ≤ X := (treeEncode_list_length xs).trans hxL
    have hpref (ys zs : List α) (he : ys ++ zs = xs) :
        (treeEncode (ys.foldl (fun c a => f (a, c)) b)).size ≤ R := by
      have h := treeEncode_append_size ys zs
      have hz := (treeEncode zs).size_pos
      rw [he] at h
      apply (hg ys b).trans
      dsimp only [R]
      gcongr
      simp only [X, treeEncode_pair, DataTree.size]
      omega
    have hW : S + 1 ≤ H * X ^ m := by
      have he : X ^ e ≤ X ^ m := Nat.pow_le_pow_right hx (by dsimp [m]; omega)
      have hm : X ≤ X ^ m := by
        simpa using Nat.pow_le_pow_right hx (show 1 ≤ m by dsimp [m]; omega)
      have hp : 1 ≤ X ^ m := Nat.one_le_pow _ _ hx
      have he' := Nat.mul_le_mul_left A he
      dsimp only [S, R, H]
      nlinarith
    have hs (ys zs : List α) (he : ys ++ zs = xs) :
        (treeEncode (zs, ys.foldl (fun c a => f (a, c)) b)).size ≤ S := by
      have h := hpref ys zs he
      have hzs := treeEncode_append_size ys zs
      have hy := (treeEncode ys).size_pos
      rw [he] at hzs
      simp only [treeEncode_pair, DataTree.size, S]
      omega
    have hb (ys : List α) (a : α) (zs : List α) (he : ys ++ a :: zs = xs) :
        P.program.time (a, ys.foldl (fun c a => f (a, c)) b) ≤
          P.coefficient * (S + 1) ^ d := by
      have hz := hs ys (a :: zs) he
      apply (P.bound _).trans
      dsimp only [d]
      gcongr
      simp only [treeEncode_pair, treeEncode_cons, DataTree.size] at hz ⊢
      omega
    have hfold := P.program.foldWork_prefix xs b S (P.coefficient * (S + 1) ^ d) hs hb
    have hbody : 10 * (S + 1) + P.coefficient * (S + 1) ^ d + 1 ≤ K * X ^ (m + m * d) := by
      have h₁ := Nat.mul_le_mul_left 10 hW
      have h₂ : P.coefficient * (S + 1) ^ d ≤ P.coefficient * H ^ d * X ^ (m * d) := by
        calc
          _ ≤ P.coefficient * (H * X ^ m) ^ d := by gcongr
          _ = _ := by rw [mul_pow, ← pow_mul]; ring
      have h := nat_poly_add X (10 * H) (P.coefficient * H ^ d) m (m * d) hx
      dsimp only [K]
      nlinarith
    have hwork : P.program.foldWork xs b ≤ K * X ^ (m + m * d + 1) := by
      calc
        _ ≤ (xs.length + 1) * (10 * (S + 1) + P.coefficient * (S + 1) ^ d + 1) := hfold
        _ ≤ X * (K * X ^ (m + m * d)) := Nat.mul_le_mul hlen hbody
        _ = _ := by rw [pow_succ]; ring
    have hout := (P.program.foldLoop_run xs b).bounds.2.1
    have hp : 1 ≤ X ^ (m + m * d + 1) := Nat.one_le_pow _ _ hx
    change P.program.foldWork xs b +
      (treeEncode (([] : List α), xs.foldl (fun c a => f (a, c)) b)).size + 1 ≤
      (2 * K + 1) * X ^ (m + m * d + 1)
    nlinarith

end ParityWL.Complexity

end OAI
