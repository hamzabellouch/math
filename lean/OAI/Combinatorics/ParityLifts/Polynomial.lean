import OAI.Combinatorics.ParityLifts.ProgramLoops

namespace OAI

namespace ParityWL.Complexity

lemma nat_poly_add (x A B a b : ℕ) (hx : 1 ≤ x) :
    A * x ^ a + B * x ^ b + 1 ≤ (A + B + 1) * x ^ (a + b) := by
  have ha : x ^ a ≤ x ^ (a + b) := Nat.pow_le_pow_right hx (by omega)
  have hb : x ^ b ≤ x ^ (a + b) := Nat.pow_le_pow_right hx (by omega)
  have h₁ := Nat.mul_le_mul_left A ha
  have h₂ := Nat.mul_le_mul_left B hb
  have h₃ : 1 ≤ x ^ (a + b) := Nat.one_le_pow _ _ hx
  nlinarith

lemma nat_poly_substitute (x A B a b : ℕ) (hx : 1 ≤ x) :
    B * (A * x ^ a + 1) ^ b ≤ B * (A + 1) ^ b * x ^ (a * b) := by
  have hp : 1 ≤ x ^ a := Nat.one_le_pow _ _ hx
  calc
    _ ≤ B * ((A + 1) * x ^ a) ^ b := by gcongr; nlinarith
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial cost is witnessed by an actual finite tree program. -/
structure PolyProgram (α β : Type) [TreeCodec α] [TreeCodec β] (f : α → β) where
  program : TreeProgram α β f
  coefficient : ℕ
  degree : ℕ
  bound : ∀ x, program.time x ≤ coefficient * ((treeEncode x).size + 1) ^ degree

def PolyProgram.of_linear {α β : Type} [TreeCodec α] [TreeCodec β] {f : α → β}
    (P : TreeProgram α β f) (C : ℕ)
    (h : ∀ x, P.time x ≤ C * ((treeEncode x).size + 1)) : PolyProgram α β f where
  program := P
  coefficient := C
  degree := 1
  bound := by simpa using h

def PolyProgram.id (α : Type) [TreeCodec α] : PolyProgram α α id :=
  .of_linear (.id α) 1 (by intro x; simp [TreeProgram.id])

def PolyProgram.const {α β : Type} [TreeCodec α] [TreeCodec β] (b : β) :
    PolyProgram α β (fun _ => b) :=
  .of_linear (.const b) (treeEncode b).size (by intro x; rfl)

def PolyProgram.fst (α β : Type) [TreeCodec α] [TreeCodec β] :
    PolyProgram (α × β) α Prod.fst :=
  .of_linear (.fst α β) 1 (by intro x; simp [TreeProgram.fst])

def PolyProgram.snd (α β : Type) [TreeCodec α] [TreeCodec β] :
    PolyProgram (α × β) β Prod.snd :=
  .of_linear (.snd α β) 1 (by intro x; simp [TreeProgram.snd])

def PolyProgram.comp {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : PolyProgram α β f) (Q : PolyProgram β γ g) :
    PolyProgram α γ (g ∘ f) where
  program := P.program.comp Q.program
  coefficient := P.coefficient + Q.coefficient * (P.coefficient + 1) ^ Q.degree + 1
  degree := P.degree + P.degree * Q.degree
  bound := by
    intro x
    let X := (treeEncode x).size + 1
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hs := (P.program.run x).bounds.2.1
    have hp := P.bound x
    have hq := Q.bound (f x)
    have ht : Q.program.time (f x) ≤
        Q.coefficient * (P.coefficient + 1) ^ Q.degree * X ^ (P.degree * Q.degree) := by
      calc
        _ ≤ Q.coefficient * (P.coefficient * X ^ P.degree + 1) ^ Q.degree := by
          apply hq.trans
          gcongr
          exact hs.trans hp
        _ ≤ _ := nat_poly_substitute X _ _ _ _ hx
    exact (Nat.add_le_add_right (Nat.add_le_add hp ht) 1).trans
      (nat_poly_add X _ _ _ _ hx)

def PolyProgram.pair {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : α → γ} (P : PolyProgram α β f) (Q : PolyProgram α γ g) :
    PolyProgram α (β × γ) (fun x => (f x, g x)) where
  program := P.program.pair Q.program
  coefficient := P.coefficient + Q.coefficient + 1
  degree := P.degree + Q.degree
  bound := by
    intro x
    exact (Nat.add_le_add_right (Nat.add_le_add (P.bound x) (Q.bound x)) 1).trans
      (nat_poly_add _ _ _ _ _ (by omega))

def PolyProgram.congr {α β : Type} [TreeCodec α] [TreeCodec β]
    {f g : α → β} (P : PolyProgram α β f) (h : ∀ x, f x = g x) :
    PolyProgram α β g := by
  have : f = g := funext h
  subst g
  exact P

def PolyProgram.ite {α β : Type} [TreeCodec α] [TreeCodec β]
    {p : α → Bool} {f g : α → β} (P : PolyProgram α Bool p)
    (F : PolyProgram α β f) (G : PolyProgram α β g) :
    PolyProgram α β (fun x => if p x then f x else g x) where
  program := P.program.ite F.program G.program
  coefficient := P.coefficient + (F.coefficient + G.coefficient + 1) + 1
  degree := P.degree + (F.degree + G.degree)
  bound := by
    intro x
    have hfg := nat_poly_add ((treeEncode x).size + 1) F.coefficient G.coefficient
      F.degree G.degree (by omega)
    have h : (if p x then F.program.time x else G.program.time x) ≤
        (F.coefficient + G.coefficient + 1) * ((treeEncode x).size + 1) ^ (F.degree + G.degree) := by
      split
      · exact (F.bound x).trans ((by omega : _ ≤ _).trans hfg)
      · exact (G.bound x).trans ((by omega : _ ≤ _).trans hfg)
    exact (Nat.add_le_add_right (Nat.add_le_add (P.bound x) h) 1).trans
      (nat_poly_add _ _ _ _ _ (by omega))

noncomputable def PolyProgram.equal (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (α × α) Bool (fun x => decide (x.1 = x.2)) where
  program := TreeProgram.equal α
  coefficient := 100 * (equalExpr.cost + 1)
  degree := 2
  bound := fun _ => le_rfl

end ParityWL.Complexity

namespace ParityWL.Complexity

def PolyProgram.expr {α β : Type} [TreeCodec α] [TreeCodec β] {f : α → β}
    (e : TExpr) (he : ∀ x, e.eval (treeEncode x) = treeEncode (f x)) : PolyProgram α β f :=
  .of_linear {
    code := e.compile
    time := fun x => e.cost * ((treeEncode x).size + 1)
    run := fun x => by simpa only [he] using e.run (treeEncode x)
  } e.cost (fun _ => le_rfl)

def PolyProgram.cons (α : Type) [TreeCodec α] :
    PolyProgram (α × List α) (List α) (fun x => x.1 :: x.2) :=
  .expr .input (fun _ => rfl)

def PolyProgram.tail (α : Type) [TreeCodec α] :
    PolyProgram (List α) (List α) List.tail :=
  .expr (TExpr.input.right) (by intro x; cases x <;> rfl)

def PolyProgram.head (α : Type) [TreeCodec α] (a : α) :
    PolyProgram (List α) α (fun x => x.headD a) :=
  .expr (.cond .input (.const (treeEncode a)) TExpr.input.left)
    (by intro x; cases x <;> rfl)

def PolyProgram.null (α : Type) [TreeCodec α] :
    PolyProgram (List α) Bool List.isEmpty :=
  .expr (.cond .input (.const (boolTree true)) .nil)
    (by intro x; cases x <;> rfl)

def PolyProgram.not : PolyProgram Bool Bool Bool.not :=
  .expr (.cond .input (.const (boolTree true)) .nil)
    (by intro x; cases x <;> rfl)

def PolyProgram.and : PolyProgram (Bool × Bool) Bool (fun x => x.1 && x.2) :=
  .expr (.cond TExpr.input.left .nil TExpr.input.right)
    (by intro x; rcases x with ⟨a, b⟩; cases a <;> rfl)

def PolyProgram.or : PolyProgram (Bool × Bool) Bool (fun x => x.1 || x.2) :=
  .expr (.cond TExpr.input.left TExpr.input.right (.const (boolTree true)))
    (by intro x; rcases x with ⟨a, b⟩; cases a <;> rfl)

lemma treeEncode_list_length {α : Type} [TreeCodec α] (xs : List α) :
    xs.length + 1 ≤ (treeEncode xs).size := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [DataTree.size]; omega

lemma treeEncode_of_mem {α : Type} [TreeCodec α] {a : α} {xs : List α} (ha : a ∈ xs) :
    (treeEncode a).size + 1 ≤ (treeEncode xs).size := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with he | ht
    · subst b; simp [DataTree.size]; omega
    · have := ih ht
      simp [DataTree.size]; omega

lemma treeEncode_append_size {α : Type} [TreeCodec α] (xs ys : List α) :
    (treeEncode (xs ++ ys)).size + 1 = (treeEncode xs).size + (treeEncode ys).size := by
  induction xs with
  | nil => simp [DataTree.size]; omega
  | cons a xs ih => simp [DataTree.size]; omega

lemma treeEncode_reverse_size {α : Type} [TreeCodec α] (xs : List α) :
    (treeEncode xs.reverse).size = (treeEncode xs).size := by
  simp only [treeEncode_list_size, List.map_reverse, List.sum_reverse]

lemma TreeProgram.foldWork_growing {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (w : α → ℕ)
    (hw : ∀ a b, (treeEncode (f (a, b))).size ≤ (treeEncode b).size + w a)
    (xs : List α) (b : β) :
    let W := (treeEncode xs).size + (treeEncode b).size + (xs.map w).sum + 1
    P.program.foldWork xs b ≤ (xs.length + 1) *
      (10 * (W + 1) + P.coefficient * (W + 1) ^ P.degree + 1) := by
  dsimp only
  induction xs generalizing b with
  | nil => simp only [foldWork, treeEncode_pair, DataTree.size, treeEncode_nil,
      List.map_nil, List.sum_nil, List.length_nil]; omega
  | cons a xs ih =>
    have hi := ih (f (a, b))
    have hg := hw a b
    let W := (treeEncode (a :: xs)).size + (treeEncode b).size +
      ((a :: xs).map w).sum + 1
    have hw' : (treeEncode xs).size + (treeEncode (f (a, b))).size +
        (xs.map w).sum + 1 ≤ W := by
      simp only [W, treeEncode_cons, DataTree.size, List.map_cons, List.sum_cons]
      omega
    have hp : P.program.time (a, b) ≤ P.coefficient * (W + 1) ^ P.degree := by
      apply (P.bound (a, b)).trans
      gcongr
      simp only [treeEncode_pair, DataTree.size, W, treeEncode_cons, List.map_cons, List.sum_cons]
      omega
    have hm : 10 * ((treeEncode xs).size + (treeEncode (f (a, b))).size + (xs.map w).sum + 1 + 1) +
        P.coefficient * ((treeEncode xs).size + (treeEncode (f (a, b))).size + (xs.map w).sum + 1 + 1) ^ P.degree + 1 ≤
          10 * (W + 1) + P.coefficient * (W + 1) ^ P.degree + 1 := by gcongr
    have hm' := Nat.mul_le_mul_left (xs.length + 1) hm
    have hstate : (treeEncode (a :: xs, b)).size ≤ W := by
      simp only [treeEncode_pair, DataTree.size, W]; omega
    change _ ≤ (List.length (a :: xs) + 1) *
      (10 * (W + 1) + P.coefficient * (W + 1) ^ P.degree + 1)
    simp only [foldWork, List.length_cons]
    nlinarith

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma list_sum_map_le {α : Type} (l : List α) (w : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ l, w x ≤ B) : (l.map w).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    nlinarith

lemma list_polynomial_sum {α : Type} [TreeCodec α] (xs : List α) (D e : ℕ) :
    (xs.map (fun a => D * ((treeEncode a).size + 1) ^ e)).sum ≤
      D * (treeEncode xs).size ^ (e + 1) := by
  have h := list_sum_map_le xs (fun a => D * ((treeEncode a).size + 1) ^ e)
    (D * (treeEncode xs).size ^ e) (by
      intro a ha
      gcongr
      exact treeEncode_of_mem ha)
  have hl := treeEncode_list_length xs
  calc
    _ ≤ xs.length * (D * (treeEncode xs).size ^ e) := h
    _ ≤ (treeEncode xs).size * (D * (treeEncode xs).size ^ e) := by gcongr; omega
    _ = _ := by rw [pow_succ]; ring

def PolyProgram.foldlGrowing {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (D e : ℕ)
    (hg : ∀ a b, (treeEncode (f (a, b))).size ≤
      (treeEncode b).size + D * ((treeEncode a).size + 1) ^ e) :
    PolyProgram (List α × β) β (fun x => x.1.foldl (fun b a => f (a, b)) x.2) where
  program := P.program.foldl
  coefficient := 2 * (10 * (D + 2) + P.coefficient * (D + 2) ^ P.degree + 1) + 1
  degree := (e + 1) + (e + 1) * P.degree + 1
  bound := by
    rintro ⟨xs, b⟩
    let X := (treeEncode (xs, b)).size + 1
    let m := e + 1
    let d := P.degree
    let H := D + 2
    let A := 10 * H + P.coefficient * H ^ d + 1
    let W := (treeEncode xs).size + (treeEncode b).size +
      (xs.map (fun a => D * ((treeEncode a).size + 1) ^ e)).sum + 1
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hxL : (treeEncode xs).size ≤ X := by simp [X, DataTree.size]; omega
    have hlen : xs.length + 1 ≤ X := (treeEncode_list_length xs).trans hxL
    have hw : W + 1 ≤ H * X ^ m := by
      have hsum := list_polynomial_sum xs D e
      have hsum' : D * (treeEncode xs).size ^ (e + 1) ≤ D * X ^ m := by
        dsimp only [m]; gcongr
      have hpow : X ≤ X ^ m := by
        simpa using Nat.pow_le_pow_right hx (show 1 ≤ m by dsimp [m]; omega)
      have hp : 1 ≤ X ^ m := Nat.one_le_pow _ _ hx
      have heq : W + 1 = X + (xs.map (fun a => D * ((treeEncode a).size + 1) ^ e)).sum := by
        simp only [W, X, treeEncode_pair, DataTree.size]
        omega
      rw [heq]
      dsimp only [H]
      nlinarith
    have hbody : 10 * (W + 1) + P.coefficient * (W + 1) ^ d + 1 ≤ A * X ^ (m + m * d) := by
      have h₁ := Nat.mul_le_mul_left 10 hw
      have h₂ : P.coefficient * (W + 1) ^ d ≤
        P.coefficient * H ^ d * X ^ (m * d) := by
        calc
          _ ≤ P.coefficient * (H * X ^ m) ^ d := by gcongr
          _ = _ := by rw [mul_pow, ← pow_mul]; ring
      have h := nat_poly_add X (10 * H) (P.coefficient * H ^ d) m (m * d) hx
      dsimp only [A]
      nlinarith
    have hfold := TreeProgram.foldWork_growing P
      (fun a => D * ((treeEncode a).size + 1) ^ e) hg xs b
    change _ ≤ (xs.length + 1) * (10 * (W + 1) + P.coefficient * (W + 1) ^ d + 1) at hfold
    have hwork : P.program.foldWork xs b ≤ A * X ^ (m + m * d + 1) := by
      calc
        _ ≤ (xs.length + 1) * (10 * (W + 1) + P.coefficient * (W + 1) ^ d + 1) := hfold
        _ ≤ X * (A * X ^ (m + m * d)) := Nat.mul_le_mul hlen hbody
        _ = _ := by rw [pow_succ]; ring
    have hout := (P.program.foldLoop_run xs b).bounds.2.1
    have hp : 1 ≤ X ^ (m + m * d + 1) := Nat.one_le_pow _ _ hx
    change P.program.foldWork xs b +
      (treeEncode (([] : List α), xs.foldl (fun c a => f (a, c)) b)).size + 1 ≤
      (2 * A + 1) * X ^ (m + m * d + 1)
    nlinarith

lemma list_fold_cons {α : Type} (xs ys : List α) :
    xs.foldl (fun b a => a :: b) ys = xs.reverse ++ ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih, List.append_assoc]

def PolyProgram.reverse (α : Type) [TreeCodec α] :
    PolyProgram (List α) (List α) List.reverse := by
  let P := (PolyProgram.cons α).foldlGrowing 1 1 (by
    intro a b
    simp [DataTree.size]
    omega)
  exact ((PolyProgram.id (List α)).pair (PolyProgram.const ([] : List α))).comp P |>.congr
    (by intro xs; simp)

def PolyProgram.append (α : Type) [TreeCodec α] :
    PolyProgram (List α × List α) (List α) (fun x => x.1 ++ x.2) := by
  let P := (PolyProgram.cons α).foldlGrowing 1 1 (by
    intro a b
    simp [DataTree.size]
    omega)
  exact (((PolyProgram.fst (List α) (List α)).comp (PolyProgram.reverse α)).pair
    (PolyProgram.snd (List α) (List α))).comp P |>.congr
      (by intro x; simp)

end ParityWL.Complexity

end OAI
