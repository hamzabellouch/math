import OAI.Combinatorics.ParityLifts.SAT

namespace OAI

namespace ParityWL.Complexity

lemma TreeProgram.loop_completes {α : Type} [TreeCodec α] {f : α → α}
    (P : TreeProgram α α f) (x : α) (n B S : ℕ)
    (hb : ∀ j, j < n → P.time (f^[j] x) ≤ B)
    (hs : ∀ j, j ≤ n → (treeEncode (f^[j] x)).size ≤ S)
    (hf : ∀ y, (treeEncode y).child false = .nil → f y = y)
    (he : (treeEncode (f^[n] x)).child false = .nil) :
    BEval (.loop P.code) (treeEncode x) ((n+1)*(B+S+1)) (treeEncode (f^[n] x)) := by
  induction n generalizing x with
  | zero =>
    simpa using (BEval.loop_stop P.code (treeEncode x) (by simpa using he)).mono
      (show (treeEncode x).size ≤ (0+1)*(B+S+1) from by
        have hx := hs 0 (by omega)
        simpa only [Function.iterate_zero, id_eq, Nat.zero_add, Nat.one_mul] using hx.trans (by omega))
  | succ n ih =>
    by_cases hx : (treeEncode x).child false = .nil
    · rw [Function.iterate_fixed (hf x hx)]
      exact (BEval.loop_stop P.code (treeEncode x) hx).mono (by
        have ht := hs 0 (by omega)
        simp only [Function.iterate_zero, id_eq] at ht
        nlinarith)
    · have ht := ih (f x)
        (fun j hj => by simpa [Function.iterate_succ_apply] using hb (j+1) (by omega))
        (fun j hj => by simpa [Function.iterate_succ_apply] using hs (j+1) (by omega))
        (by simpa [Function.iterate_succ_apply] using he)
      have h₀ := (P.run x).mono (by simpa using hb 0 (by omega))
      simpa [Function.iterate_succ_apply] using (BEval.loop_next hx h₀ ht).mono
        (show B+(n+1)*(B+S+1)+1 ≤ (n+1+1)*(B+S+1) by nlinarith)

def streamStep {α : Type} (p : List Bool → α × List Bool) (x : List Bool × List α) :
    List Bool × List α :=
  if x.1 = [] then x else ((p x.1).2, (p x.1).1 :: x.2)

lemma streamStep_fixed {α : Type} (p : List Bool → α × List Bool) (xs : List α) :
    streamStep p ([],xs) = ([],xs) := by simp [streamStep]

lemma streamStep_remaining {α : Type} (p : List Bool → α × List Bool)
    (hp : ∀ xs, xs≠[] → (p xs).2.length < xs.length) (n : ℕ) (x : List Bool × List α) :
    ((streamStep p)^[n] x).1.length ≤ x.1.length-n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hj := ih (streamStep p x)
    by_cases hx : x.1=[]
    · simpa [streamStep, hx] using hj
    · have hs := hp x.1 hx
      simpa only [streamStep, ite_eq_right hx] using hj.trans (show (streamStep p x).1.length-n ≤ x.1.length-(n+1) by
        simp only [streamStep, ite_eq_right hx]
        omega)

lemma streamStep_potential {α : Type} [TreeCodec α] (p : List Bool → α × List Bool) (D : ℕ)
    (hp : ∀ xs, xs≠[] → (treeEncode (p xs).1).size+1+D*(p xs).2.length ≤ D*xs.length)
    (n : ℕ) (x : List Bool × List α) :
    D*((streamStep p)^[n] x).1.length + (treeEncode ((streamStep p)^[n] x).2).size ≤
      D*x.1.length+(treeEncode x.2).size := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply (ih (streamStep p x)).trans
    by_cases hx : x.1=[]
    · simp [streamStep, hx]
    · have h := hp x.1 hx
      simp only [streamStep, ite_eq_right hx, treeEncode_cons, DataTree.size]
      omega

def streamRun {α : Type} (p : List Bool → α × List Bool) (xs : List Bool) : List Bool × List α :=
  (streamStep p)^[xs.length] (xs,[])

def parseStream {α : Type} (p : List Bool → α × List Bool) (xs : List Bool) : List α :=
  (streamRun p xs).2.reverse

def PolyProgram.streamStep {α : Type} [TreeCodec α] {p : List Bool → α × List Bool}
    (P : PolyProgram (List Bool) (α × List Bool) p) :
    PolyProgram (List Bool × List α) (List Bool × List α) (streamStep p) := by
  let F := PolyProgram.fst (List Bool) (List α)
  let G := PolyProgram.snd (List Bool) (List α)
  let E : PolyProgram ((α × List Bool) × List α) (List Bool × List α)
      (fun x => (x.1.2,x.1.1::x.2)) :=
    .expr (.pair TExpr.input.left.right (.pair TExpr.input.left.left TExpr.input.right))
      (by intro x; rfl)
  let Q := ((F.comp P).pair G).comp E
  refine ((F.comp (PolyProgram.null Bool)).ite (PolyProgram.id _) Q).congr ?_
  rintro ⟨xs,ys⟩
  cases xs <;> simp [Complexity.streamStep, List.isEmpty]

def PolyProgram.streamRun {α : Type} [TreeCodec α] {p : List Bool → α × List Bool}
    (P : PolyProgram (List Bool) (α × List Bool) p) (D : ℕ)
    (hc : ∀ xs, xs≠[] → (p xs).2.length < xs.length)
    (ha : ∀ xs, xs≠[] → (treeEncode (p xs).1).size+1+D*(p xs).2.length ≤ D*xs.length) :
    PolyProgram (List Bool) (List Bool × List α) (streamRun p) := by
  let Q := P.streamStep
  let d := Q.degree
  let a := Q.coefficient*(D+9)^d
  let A := a+D+20
  refine ⟨⟨.seq (.pair .id .nil) (.loop Q.program.code),
    (fun xs => A*((treeEncode xs).size+1)^(d+2)), ?_⟩, A, d+2, fun _ => le_rfl⟩
  intro xs
  let X := (treeEncode xs).size+1
  let S := (D+8)*X
  let B := a*X^d
  have hx : 1 ≤ X := by dsimp [X]; have := (treeEncode xs).size_pos; omega
  have hL : xs.length+1 ≤ X := by have := treeEncode_list_length xs; dsimp [X]; omega
  have hs (j : ℕ) : (treeEncode ((Complexity.streamStep p)^[j] (xs,([]:List α)))).size ≤ S := by
    have hr := streamStep_remaining p hc j (xs,([]:List α))
    have ha := streamStep_potential p D ha j (xs,([]:List α))
    have hl := treeEncode_bits_size ((Complexity.streamStep p)^[j] (xs,([]:List α))).1
    simp only [treeEncode_nil, DataTree.size] at ha
    have hlen : ((Complexity.streamStep p)^[j] (xs,([]:List α))).1.length ≤ xs.length := hr.trans (Nat.sub_le _ _)
    have hacc : (treeEncode ((Complexity.streamStep p)^[j] (xs,([]:List α))).2).size ≤ D*xs.length+1 := by omega
    change _ ≤ S
    rw [treeEncode_prod, DataTree.size]
    dsimp only [S]
    nlinarith [Nat.mul_le_mul_left D (show xs.length ≤ X from by omega)]
  have hb (j : ℕ) : Q.program.time ((Complexity.streamStep p)^[j] (xs,([]:List α))) ≤ B := by
    apply (Q.bound _).trans
    change _ ≤ Q.coefficient*(D+9)^d*X^d
    have ht := hs j
    have he : (treeEncode ((Complexity.streamStep p)^[j] (xs,([]:List α)))).size+1 ≤ (D+9)*X := by
      change (treeEncode ((Complexity.streamStep p)^[j] (xs,([]:List α)))).size ≤ (D+8)*X at ht
      nlinarith
    calc
      _ ≤ Q.coefficient*((D+9)*X)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he _)
      _ = _ := by rw [mul_pow]; ring
  have he : (treeEncode ((Complexity.streamStep p)^[xs.length] (xs,([]:List α)))).child false = .nil := by
    have hr := streamStep_remaining p hc xs.length (xs,([]:List α))
    have hn : ((Complexity.streamStep p)^[xs.length] (xs,([]:List α))).1=[] := by
      apply List.length_eq_zero_iff.mp
      simp only [Nat.sub_self, Nat.le_zero_eq] at hr
      exact hr
    simp [treeEncode_prod, DataTree.child, hn]
  have hf : ∀ y : List Bool × List α, (treeEncode y).child false = .nil → Complexity.streamStep p y=y := by
    rintro ⟨ys,zs⟩ hh
    cases ys with
    | nil => exact streamStep_fixed _ _
    | cons b ys => simp [DataTree.child] at hh
  have hr := Q.program.loop_completes (xs,[]) xs.length B S (fun j _ => hb j) (fun j _ => hs j) hf he
  have hi := (BEval.id (treeEncode xs)).pair (BEval.nil (treeEncode xs))
  have hi' : BEval (.pair .id .nil) (treeEncode xs) (2*(treeEncode xs).size+1)
      (treeEncode (xs,([]:List α))) := by simpa [two_mul] using hi
  apply (hi'.seq hr).mono
  change 2*(treeEncode xs).size+1+(xs.length+1)*(B+S+1)+1 ≤ A*X^(d+2)
  have hpow₁ : X ≤ X^(d+1) := by simpa using Nat.pow_le_pow_right hx (show 1 ≤ d+1 by omega)
  have hpowd : X^d ≤ X^(d+1) := Nat.pow_le_pow_right hx (by omega)
  have hp : 1 ≤ X^(d+1) := Nat.one_le_pow _ _ hx
  have hBS : B+S+1 ≤ (a+D+9)*X^(d+1) := by
    dsimp [B,S]
    nlinarith [Nat.mul_le_mul_left a hpowd, Nat.mul_le_mul_left (D+8) hpow₁]
  have hm := Nat.mul_le_mul hL hBS
  have hid : X*((a+D+9)*X^(d+1)) = (a+D+9)*X^(d+2) := by rw [show d+2=(d+1)+1 by omega, pow_succ]; ring
  rw [hid] at hm
  have hp' : X ≤ X^(d+2) := by simpa using Nat.pow_le_pow_right hx (show 1 ≤ d+2 by omega)
  have heX : (treeEncode xs).size+1=X := rfl
  dsimp only [A]
  nlinarith

def PolyProgram.parseStream {α : Type} [TreeCodec α] {p : List Bool → α × List Bool}
    (P : PolyProgram (List Bool) (α × List Bool) p) (D : ℕ)
    (hc : ∀ xs, xs≠[] → (p xs).2.length < xs.length)
    (ha : ∀ xs, xs≠[] → (treeEncode (p xs).1).size+1+D*(p xs).2.length ≤ D*xs.length) :
    PolyProgram (List Bool) (List α) (parseStream p) :=
  ((P.streamRun D hc ha).comp (PolyProgram.snd (List Bool) (List α))).comp (PolyProgram.reverse α)

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma streamStep_chunks {α β : Type} (p : List Bool → β × List Bool)
    (enc : α → List Bool) (val : α → β)
    (hp : ∀ a xs, p (enc a ++ xs) = (val a,xs))
    (he : ∀ a, enc a ≠ []) (as : List α) (bs : List β) :
    (streamStep p)^[as.length] (as.flatMap enc,bs) = ([], (as.map val).reverse ++ bs) := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hne : (a::as).flatMap enc ≠ [] := by simp [he a]
    simp only [List.flatMap_cons] at hne
    simp only [streamStep, List.flatMap_cons, hne, ↓reduceIte, hp]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

lemma chunks_length {α : Type} (enc : α → List Bool) (he : ∀ a, enc a ≠ []) (as : List α) :
    as.length ≤ (as.flatMap enc).length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have hn := List.length_pos_iff_ne_nil.mpr (he a)
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

lemma parseStream_chunks {α β : Type} (p : List Bool → β × List Bool)
    (enc : α → List Bool) (val : α → β)
    (hp : ∀ a xs, p (enc a ++ xs) = (val a,xs))
    (he : ∀ a, enc a ≠ []) (as : List α) :
    parseStream p (as.flatMap enc) = as.map val := by
  have hl := chunks_length enc he as
  have hk : (as.flatMap enc).length = ((as.flatMap enc).length-as.length)+as.length := by omega
  unfold parseStream streamRun
  rw [hk, Function.iterate_add_apply, streamStep_chunks p enc val hp he]
  rw [Function.iterate_fixed (streamStep_fixed p _)]
  simp

lemma encodeNat_ne_nil (n : ℕ) : encodeNat n ≠ [] := by simp [encodeNat]

lemma encodeClause_ne_nil {N : ℕ} (C : Clause N) : encodeClause C ≠ [] := by
  simp [encodeClause, encodeNat_ne_nil]

def parseClauses (xs : List Bool) : List BitClause := parseStream readClause xs

noncomputable def PolyProgram.parseClauses : PolyProgram (List Bool) (List BitClause) parseClauses :=
  PolyProgram.readClause.parseStream 40 readClause_consumes readClause_account

lemma parseClauses_encode {N : ℕ} (F : Formula N) :
    parseClauses (F.flatMap encodeClause) = F.map (fun C => C.literals.map (fun l => (l.1.val.bits,l.2))) :=
  parseStream_chunks readClause encodeClause _ readClause_encode encodeClause_ne_nil F

def parseFormula (xs : List Bool) : List BitClause :=
  parseClauses (readNatBits (readNatBits xs).2).2

noncomputable def PolyProgram.parseFormula : PolyProgram (List Bool) (List BitClause) parseFormula := by
  let P := PolyProgram.readNatBits.comp (PolyProgram.snd (List Bool) (List Bool))
  exact (P.comp P).comp PolyProgram.parseClauses

lemma parseFormula_encode {N : ℕ} (F : Formula N) :
    parseFormula (encodeFormula F) = F.map (fun C => C.literals.map (fun l => (l.1.val.bits,l.2))) := by
  simp [parseFormula, encodeFormula, List.append_assoc, readNatBits_encode, parseClauses_encode]

end ParityWL.Complexity

end OAI
