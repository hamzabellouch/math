import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricBoxFactorization {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  nonnegative : 0 ≤ p
  [topology : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [hausdorff : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  basis : Basis (Fin (finrank ℚ (Fin 8 → W.L))) ℚ (Fin 8 → W.L)
  weight : Fin (finrank ℚ (Fin 8 → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : Fin 8 => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  height : ∀ i j, rationalLogHeight ((pi (fun _ : Fin 8 => W.model)).basis.repr (basis i) j) ≤ q
  factorization : (pi (fun _ : Fin 8 => W.model)).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency W.antisymmetricBoxFrequencies) (fun _ : Fin 4 => (N : ℝ))
    ((W.antisymmetricBoxNiltest nonnegative leftIndex rightIndex).symbol basis weight adapted) q

noncomputable def NativeAntisymmetricBoxFactorization.mono {p p' q q' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
    (V : NativeAntisymmetricBoxFactorization W N q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeAntisymmetricBoxFactorization (W.mono hp) N q' := by
  letI := V.topology
  letI := V.topologicalAdd
  letI := V.continuousSMul
  letI := V.hausdorff
  letI : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → (W.mono hp).L)) := V.topology
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → (W.mono hp).L)) := V.topologicalAdd
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → (W.mono hp).L)) := V.continuousSMul
  letI : T2Space (ℝ ⊗[ℚ] (Fin 8 → (W.mono hp).L)) := V.hausdorff
  have hfactor := NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi (fun _ : Fin 8 => W.model)).filtration V.basis V.weight V.adapted V.factorization hq
    (fun _ => by exact_mod_cast NeZero.pos N)
  have horbit :
      ((W.mono hp).antisymmetricBoxNiltest (V.nonnegative.trans hp) V.leftIndex V.rightIndex).orbit =
        (W.antisymmetricBoxNiltest V.nonnegative V.leftIndex V.rightIndex).orbit := by
    apply congrArg (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 => W.model.filtration))
    funext k
    fin_cases k <;> rfl
  have hsymbol :
      ((W.mono hp).antisymmetricBoxNiltest (V.nonnegative.trans hp) V.leftIndex V.rightIndex).symbol
          V.basis V.weight V.adapted =
        (W.antisymmetricBoxNiltest V.nonnegative V.leftIndex V.rightIndex).symbol
          V.basis V.weight V.adapted := by
    unfold Niltest.symbol
    apply congrArg ((pi (fun _ : Fin 8 => W.model)).filtration.realPolynomialSymbolHom
      V.basis V.weight V.adapted (fun _ : Fin 4 => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : (pi (fun _ : Fin 8 => W.model)).filtration.realification.PolynomialOrbit
      (fun _ : Fin 4 => 1) => o.log) horbit
  have htransport := (congrArg (fun symbol =>
    (pi (fun _ : Fin 8 => W.model)).filtration.ControlledSymbolFactorization
      V.basis V.weight V.adapted (piFrequency W.antisymmetricBoxFrequencies)
      (fun _ : Fin 4 => (N : ℝ)) symbol q') hsymbol).mpr hfactor
  exact {
    leftIndex := V.leftIndex
    rightIndex := V.rightIndex
    nonnegative := V.nonnegative.trans hp
    topology := V.topology
    topologicalAdd := V.topologicalAdd
    continuousSMul := V.continuousSMul
    hausdorff := V.hausdorff
    basis := V.basis
    weight := V.weight
    adapted := V.adapted
    height := fun i j => (V.height i j).trans hq
    factorization := htransport }

theorem exists_antisymmetric_box_step_drop_indices :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x))).re →
      ∃ V : NativeAntisymmetricBoxFactorization W N ((p + C) ^ C),
        V.leftIndex = i ∧ V.rightIndex = j := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ k, mixedCorrelationDegree 1 k)
    (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 8
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hN hbox
  let r := productNiltestBudget (p + 8) + p + 4
  have hprod : 0 ≤ productNiltestBudget (p + 8) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have h4r : 4 ≤ r := by dsimp [r]; linarith
  have hTr : productNiltestBudget (p + 8) ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, R, r, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + C) ^ C := by linarith
  have hfactor : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology
    (productFinBasis (fun _ : Fin 8 => W.model))
  let : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L)) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htM
  let : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htT
  let D := pi (fun _ : Fin 8 => W.model)
  let T := W.antisymmetricBoxNiltest hp i j
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T ((W.antisymmetricBoxNiltest_complexity hp i j).mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 4 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 4 => N) = integerBox (fun _ : Fin 4 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero, show T = W.antisymmetricBoxNiltest hp i j from rfl, W.antisymmetricBoxNiltest_mean]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hbox.trans (Complex.re_le_norm _))
  have hf := hconstruct (piFrequency W.antisymmetricBoxFrequencies)
    (W.antisymmetricBoxNiltest_vertical hp i j) 0 (fun _ : Fin 4 => N)
    (fun _ => NeZero.pos N) (by simpa using h4r)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    leftIndex := i
    rightIndex := j
    nonnegative := hp
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun i j => (he i j).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }, rfl, rfl⟩

theorem exists_antisymmetric_box_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x))).re →
      Nonempty (NativeAntisymmetricBoxFactorization W N ((p + C) ^ C)) := by
  obtain ⟨C, hC, h⟩ := exists_antisymmetric_box_step_drop_indices
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hN hbox
  obtain ⟨V, _, _⟩ := h hp W i j hN hbox
  exact ⟨V⟩

end Erdos3

end

end OAI
