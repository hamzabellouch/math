import OAI.Combinatorics.ParityLifts.Simulator

namespace OAI

namespace ParityWL.Complexity

lemma BEval.loop_completes (p : FCode) (f : DataTree → DataTree) (x : DataTree)
    (n B S : ℕ)
    (hb : ∀ j, j < n → BEval p (f^[j] x) B (f^[j + 1] x))
    (hs : ∀ j, j ≤ n → (f^[j] x).size ≤ S)
    (hf : ∀ y, y.child false = .nil → f y = y)
    (he : (f^[n] x).child false = .nil) :
    BEval (.loop p) x ((n + 1) * (B + S + 1)) (f^[n] x) := by
  induction n generalizing x with
  | zero =>
    simpa using (BEval.loop_stop p x (by simpa using he)).mono
      (show x.size ≤ (0 + 1) * (B + S + 1) from by
        have hx : x.size ≤ S := by simpa using hs 0 (by omega)
        omega)
  | succ n ih =>
    by_cases hx : x.child false = .nil
    · rw [Function.iterate_fixed (hf x hx)]
      exact (BEval.loop_stop p x hx).mono (by
        have h := hs 0 (by omega)
        simp only [Function.iterate_zero, id_eq] at h
        nlinarith)
    · have ht := ih (f x)
        (fun j hj => by simpa [Function.iterate_succ_apply] using hb (j + 1) (by omega))
        (fun j hj => by simpa [Function.iterate_succ_apply] using hs (j + 1) (by omega))
        (by simpa [Function.iterate_succ_apply] using he)
      have h₀ : BEval p x B (f x) := by simpa using hb 0 (by omega)
      have h := BEval.loop_next hx h₀ ht
      simpa [Function.iterate_succ_apply] using h.mono
        (show B + (n + 1) * (B + S + 1) + 1 ≤ (n + 1 + 1) * (B + S + 1) by nlinarith)

def smallControl (M : Machine) (x : SmallConfiguration M) : Bool × SmallConfiguration M :=
  ((M.output x.1).isNone, x)

def simStepExpr (M : Machine) : TExpr :=
  .cond TExpr.input.left .input
    (.pair (TExpr.smallContinue M (TExpr.smallStep M TExpr.input.right))
      (TExpr.smallStep M TExpr.input.right))

def simStartExpr (M : Machine) : TExpr := .pair (TExpr.smallContinue M .input) .input

def simAnswerExpr (M : Machine) : TExpr := TExpr.smallAnswer M TExpr.input.right

lemma simStartExpr_eval (M : Machine) (x : SmallConfiguration M) :
    (simStartExpr M).eval (treeEncode x) = treeEncode (smallControl M x) := by
  simp only [simStartExpr, TExpr.eval, TExpr.smallContinue_eval M .input _ x rfl]
  rfl

lemma simStepExpr_fixed (M : Machine) (x : DataTree) (h : x.child false = .nil) :
    (simStepExpr M).eval x = x := by simp [simStepExpr, TExpr.eval, h]

lemma simStepExpr_eval (M : Machine) (x : SmallConfiguration M) :
    (simStepExpr M).eval (treeEncode (smallControl M x)) =
      treeEncode (smallControl M (smallStep M x)) := by
  have hr : TExpr.input.right.eval (treeEncode (smallControl M x)) = treeEncode x := rfl
  have hn := TExpr.smallStep_eval M TExpr.input.right _ x hr
  have hc := TExpr.smallContinue_eval M (TExpr.smallStep M TExpr.input.right) _ (smallStep M x) hn
  cases ho : M.output x.1 with
  | some b =>
    simp [simStepExpr, TExpr.eval, smallControl, ho, smallStep, treeEncode_prod, DataTree.child]
  | none =>
    change (if (treeEncode (smallControl M x)).child false = .nil then _ else _) = _
    have hg : (treeEncode (smallControl M x)).child false ≠ .nil := by
      simp [smallControl, ho, DataTree.child]
    rw [ite_eq_right hg]
    change DataTree.node _ _ = _
    rw [hn, hc]
    rfl

lemma simStepExpr_iterate (M : Machine) (x : SmallConfiguration M) (n : ℕ) :
    ((simStepExpr M).eval)^[n] (treeEncode (smallControl M x)) =
      treeEncode (smallControl M ((smallStep M)^[n] x)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, simStepExpr_eval, Function.iterate_succ_apply']

lemma smallControl_size (M : Machine) (x : SmallConfiguration M) :
    (treeEncode (smallControl M x)).size ≤ (treeEncode x).size + 4 := by
  simp only [smallControl, treeEncode_pair, DataTree.size]
  cases (M.output x.1).isNone <;> simp [DataTree.size] <;> omega

lemma simLoop_run {M : Machine} {xs : List Bool} {s : ℕ} {b : Bool}
    (h : Emits M xs s b) :
    let C := 2 * M.extraStates + (M.tapes + 1) * (4 * M.extraSymbols + 16) + 4
    BEval (.loop (simStepExpr M).compile) (treeEncode (smallControl M (smallInitial M xs)))
      (((simStepExpr M).cost + 2) * (C + 5) * (xs.length + s + 1)^2)
      (treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M xs)))) := by
  dsimp only
  let C := 2 * M.extraStates + (M.tapes + 1) * (4 * M.extraSymbols + 16) + 4
  let X := xs.length + s + 1
  let S := (C+4)*X
  have hs (j : ℕ) (hj : j ≤ s) :
      (((simStepExpr M).eval)^[j] (treeEncode (smallControl M (smallInitial M xs)))).size ≤ S := by
    rw [simStepExpr_iterate]
    have hsz := smallControl_size M ((smallStep M)^[j] (smallInitial M xs))
    have ht := smallRun_size M xs j
    change _ ≤ C * (xs.length+j+1) at ht
    have hm : C * (xs.length+j+1) ≤ C*X := Nat.mul_le_mul_left C (by dsimp [X]; omega)
    dsimp only [S]
    have hx : 1 ≤ X := by dsimp [X]; omega
    nlinarith
  have hr := BEval.loop_completes (simStepExpr M).compile (simStepExpr M).eval
    (treeEncode (smallControl M (smallInitial M xs))) s ((simStepExpr M).cost*(S+1)) S
    (fun j hj => by
      rw [Function.iterate_succ_apply']
      exact ((simStepExpr M).run _).mono (Nat.mul_le_mul_left _ (by have := hs j (by omega); omega)))
    hs (simStepExpr_fixed M) (by
      rw [simStepExpr_iterate]
      simp [smallControl, smallRun_output h, DataTree.child])
  rw [simStepExpr_iterate] at hr
  apply hr.mono
  change (s+1)*((simStepExpr M).cost*(S+1)+S+1) ≤
    ((simStepExpr M).cost+2)*(C+5)*X^2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hn : s+1 ≤ X := by dsimp [X]; omega
  have hb : (simStepExpr M).cost*(S+1)+S+1 ≤ ((simStepExpr M).cost+2)*(C+5)*X := by
    dsimp [S]
    nlinarith
  calc
    _ ≤ X * (((simStepExpr M).cost+2)*(C+5)*X) := Nat.mul_le_mul hn hb
    _ = _ := by ring

def smallInitialExpr (M : Machine) : TExpr :=
  .pair (.const (treeEncode M.initial)) (.tuple (M.tapes+1)
    (fun i => .pair .nil (if i.val = 0 then .input else .nil)))

def smallBitProgram (M : Machine) : PolyProgram Bool (Fin (M.extraSymbols+3)) (inputSymbol M) :=
  .expr (.cond .input (.const (numTree 1)) (.const (numTree 2)))
    (by intro b; cases b <;> rfl)

def smallInitialProgram (M : Machine) :
    PolyProgram (List Bool) (SmallConfiguration M) (smallInitial M) := by
  let B := (smallBitProgram M).map
  let E : PolyProgram (List (Fin (M.extraSymbols+3))) (SmallConfiguration M)
      (fun xs => (M.initial, fun i => ([], if i.val = 0 then xs else []))) :=
    .expr (smallInitialExpr M) (by
      intro xs
      simp only [smallInitialExpr, TExpr.eval, treeEncode_pair]
      congr 1
      apply TExpr.tuple_eval
      intro i
      by_cases hi : i.val=0 <;> simp [hi, TExpr.eval])
  exact B.comp E

lemma PolyProgram.congr_degree {α β : Type} [TreeCodec α] [TreeCodec β]
    {f g : α → β} (P : PolyProgram α β f) (h : ∀ x, f x = g x) :
    (P.congr h).degree = P.degree := by
  have he : f = g := funext h
  subst g
  rfl

lemma PolyProgram.reverse_degree (α : Type) [TreeCodec α] :
    (PolyProgram.reverse α).degree = 12 := by
  simp only [PolyProgram.reverse, PolyProgram.congr_degree, PolyProgram.comp,
    PolyProgram.pair, PolyProgram.id, PolyProgram.const, PolyProgram.foldlGrowing,
    PolyProgram.cons, PolyProgram.expr, PolyProgram.of_linear]

lemma PolyProgram.map_degree {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → β} (P : PolyProgram α β f) :
    P.map.degree = 13 * (4 * P.degree^2 + 18 * P.degree + 24) := by
  simp only [PolyProgram.map, PolyProgram.congr_degree, PolyProgram.comp,
    PolyProgram.pair, PolyProgram.id, PolyProgram.const, PolyProgram.foldlGrowing,
    PolyProgram.cons, PolyProgram.expr, PolyProgram.of_linear,
    PolyProgram.fst, PolyProgram.snd, PolyProgram.reverse_degree]
  ring

def smallInitialDegree : ℕ := 1196

lemma smallInitialProgram_degree (M : Machine) :
    (smallInitialProgram M).degree = smallInitialDegree := by
  simp only [smallInitialProgram, PolyProgram.comp, PolyProgram.map_degree, smallBitProgram,
    PolyProgram.expr, PolyProgram.of_linear, smallInitialDegree]
  norm_num

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma treeEncode_bits_size (bs : List Bool) : (treeEncode bs).size ≤ 4 * bs.length + 1 := by
  induction bs with
  | nil => simp [DataTree.size]
  | cons b bs ih => cases b <;> simp [DataTree.size] <;> omega

def simulationCode (M : Machine) : FCode :=
  .seq (smallInitialProgram M).program.code
    (.seq (simStartExpr M).compile
      (.seq (.loop (simStepExpr M).compile) (simAnswerExpr M).compile))

def simulationDegree : ℕ := smallInitialDegree + 2

def simulationCoefficient (M : Machine) : ℕ :=
  let C := 2 * M.extraStates + (M.tapes + 1) * (4 * M.extraSymbols + 16) + 4
  (smallInitialProgram M).coefficient * 4 ^ smallInitialDegree +
    (simStartExpr M).cost * (C + 1) +
    ((simStepExpr M).cost + 2) * (C + 5) +
    (simAnswerExpr M).cost * (C + 5) + 3

lemma simulation_run {M : Machine} {bs : List Bool} {s : ℕ} {b : Bool}
    (h : Emits M bs s b) :
    BEval (simulationCode M) (treeEncode bs)
      (simulationCoefficient M * (bs.length + s + 1)^simulationDegree) (treeEncode b) := by
  let C := 2 * M.extraStates + (M.tapes + 1) * (4 * M.extraSymbols + 16) + 4
  let X := bs.length + s + 1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hpow (j : ℕ) (hj : j ≤ simulationDegree) : X^j ≤ X^simulationDegree :=
    Nat.pow_le_pow_right hx hj
  have hp : 1 ≤ X^simulationDegree := Nat.one_le_pow _ _ hx
  have hl : bs.length + 1 ≤ X := by dsimp [X]; omega
  have hint := (smallInitialProgram M).program.run bs
  have hinit : (smallInitialProgram M).program.time bs ≤
      (smallInitialProgram M).coefficient * 4^smallInitialDegree * X^simulationDegree := by
    have hsz : (treeEncode bs).size+1 ≤ 4*X := by
      have := treeEncode_bits_size bs
      dsimp [X]
      omega
    calc
      _ ≤ (smallInitialProgram M).coefficient * ((treeEncode bs).size+1)^smallInitialDegree := by
        simpa only [smallInitialProgram_degree] using (smallInitialProgram M).bound bs
      _ ≤ (smallInitialProgram M).coefficient * (4*X)^smallInitialDegree := by gcongr
      _ = (smallInitialProgram M).coefficient * 4^smallInitialDegree * X^smallInitialDegree := by rw [mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hpow _ (by dsimp [simulationDegree]; omega))
  have hs₀ : (treeEncode (smallInitial M bs)).size+1 ≤ (C+1)*X := by
    have hq := smallRun_size M bs 0
    simp only [Function.iterate_zero, id_eq, Nat.add_zero] at hq
    change _ ≤ C*(bs.length+1) at hq
    nlinarith [Nat.mul_le_mul_left C hl]
  have hs₁ : (treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M bs)))).size+1 ≤
      (C+5)*X := by
    have hq := smallRun_size M bs s
    change _ ≤ C*X at hq
    have hr := smallControl_size M ((smallStep M)^[s] (smallInitial M bs))
    nlinarith
  have hstart := (simStartExpr M).run (treeEncode (smallInitial M bs))
  rw [simStartExpr_eval] at hstart
  have ha := (simAnswerExpr M).run
    (treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M bs))))
  have hea : (simAnswerExpr M).eval
      (treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M bs)))) = treeEncode b := by
    rw [simAnswerExpr, TExpr.smallAnswer_eval M TExpr.input.right _ _ rfl]
    change boolTree ((M.output ((smallStep M)^[s] (smallInitial M bs)).1).getD false) = _
    rw [smallRun_output h]
    rfl
  rw [hea] at ha
  have hr := hint.seq (hstart.seq ((simLoop_run h).seq ha))
  change BEval (simulationCode M) _ _ _ at hr
  apply hr.mono
  have hp₁ : X ≤ X^simulationDegree := by simpa using hpow 1 (by decide)
  have hp₂ := hpow 2 (by dsimp [simulationDegree]; omega)
  have hb₁ := Nat.mul_le_mul_left (simStartExpr M).cost hs₀
  have hb₂ := Nat.mul_le_mul_left (simAnswerExpr M).cost hs₁
  have hstart' : (simStartExpr M).cost*((treeEncode (smallInitial M bs)).size+1) ≤
      (simStartExpr M).cost*(C+1)*X^simulationDegree := by
    calc
      _ ≤ (simStartExpr M).cost*(C+1)*X := by simpa [mul_assoc] using hb₁
      _ ≤ _ := Nat.mul_le_mul_left _ hp₁
  have hans : (simAnswerExpr M).cost *
      ((treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M bs)))).size+1) ≤
      (simAnswerExpr M).cost*(C+5)*X^simulationDegree := by
    calc
      _ ≤ (simAnswerExpr M).cost*(C+5)*X := by simpa [mul_assoc] using hb₂
      _ ≤ _ := Nat.mul_le_mul_left _ hp₁
  have hloop := Nat.mul_le_mul_left (((simStepExpr M).cost+2)*(C+5)) hp₂
  change _ ≤ simulationCoefficient M * X^simulationDegree
  change (smallInitialProgram M).program.time bs +
    ((simStartExpr M).cost*((treeEncode (smallInitial M bs)).size+1) +
      (((simStepExpr M).cost+2)*(C+5)*X^2 +
      (simAnswerExpr M).cost*((treeEncode (smallControl M ((smallStep M)^[s] (smallInitial M bs)))).size+1)+1)+1)+1 ≤
    ((smallInitialProgram M).coefficient*4^smallInitialDegree +
      (simStartExpr M).cost*(C+1)+((simStepExpr M).cost+2)*(C+5)+(simAnswerExpr M).cost*(C+5)+3)*X^simulationDegree
  nlinarith

noncomputable def Machine.preprocess (M : Machine) (p : FCode) : Machine := (FCode.seq p (simulationCode M)).decision

def preprocessingDegree : ℕ := 2*simulationDegree

lemma Machine.preprocess_run (M : Machine) (p : FCode) :
    ∃ C : ℕ, 0 < C ∧ ∀ (xs ys : List Bool) (B s : ℕ) (b : Bool),
      BEval p (treeEncode xs) B (treeEncode ys) → Emits M ys s b →
      ∃ r, Emits (M.preprocess p) xs r b ∧
        r ≤ C*(B+xs.length+s+1)^preprocessingDegree := by
  let d := simulationDegree
  let A := simulationCoefficient M + 2
  let q := FCode.seq p (simulationCode M)
  let K := 500*(q.factor+2)*(q.depth+2)
  refine ⟨K*(A+1)^2+65, by omega, ?_⟩
  intro xs ys B s b hp hm
  have hyr : ys.length ≤ B := by
    have hl := treeEncode_list_length ys
    have hb := hp.bounds.2
    omega
  have hs := simulation_run hm
  have hr := hp.seq hs
  rw [treeEncode_bits] at hr
  obtain ⟨r, hb, he⟩ := hr.decision
  have he' : Emits (M.preprocess p) xs r b := by
    cases b <;> simpa [Machine.preprocess] using he
  refine ⟨r, he', hb.trans ?_⟩
  let X := B+xs.length+s+1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hp₁ : X ≤ X^d := by
    simpa using Nat.pow_le_pow_right hx (show 1 ≤ d from by decide)
  have hp₀ : 1 ≤ X^d := Nat.one_le_pow _ _ hx
  have hB : B ≤ X^d := (show B ≤ X by dsimp [X]; omega).trans hp₁
  have hY : (ys.length+s+1)^d ≤ X^d := Nat.pow_le_pow_left (by dsimp [X]; omega) _
  have hcost : B+simulationCoefficient M*(ys.length+s+1)^d+1 ≤ A*X^d := by
    dsimp [A]
    nlinarith [Nat.mul_le_mul_left (simulationCoefficient M) hY]
  have hcost' : B+simulationCoefficient M*(ys.length+s+1)^d+1+1 ≤ (A+1)*X^d := by nlinarith
  have hsquare := Nat.pow_le_pow_left hcost' 2
  have hx₂ : X^d ≤ X^(2*d) := Nat.pow_le_pow_right hx (by omega)
  have hL : xs.length ≤ X^(2*d) := (show xs.length ≤ X by dsimp [X]; omega).trans (hp₁.trans hx₂)
  have h1 : 1 ≤ X^(2*d) := Nat.one_le_pow _ _ hx
  have hc := Nat.mul_le_mul_left K hsquare
  rw [mul_pow, ← pow_mul] at hc
  have hed : d*2 = 2*d := by omega
  rw [hed] at hc
  change K*((B+simulationCoefficient M*(ys.length+s+1)^d+1)+1)^2+44*xs.length+20 ≤ _
  change _ ≤ (K*(A+1)^2+65)*X^(2*d)
  nlinarith

end ParityWL.Complexity

end OAI
