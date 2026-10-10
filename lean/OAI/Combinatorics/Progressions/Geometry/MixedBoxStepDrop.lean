import OAI.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop

namespace OAI

section

namespace Erdos3

abbrev MixedBoxIndex (n : ℕ) := Fin (n + 2) × Bool

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

noncomputable def mixedBoxComponent (out : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n) :
    W.model.Niltest (fun _ : MixedBoxIndex n => 1) :=
  (W.component out).linearPullbackHom (fun j =>
    { toFun := fun x => x (mixedSlotInput (v 0) (v 1) (fun l => v l.succ.succ) j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl })

theorem mixedBoxComponent_eval (out : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (x : MixedBoxIndex n → ℤ) :
    (W.mixedBoxComponent out v).eval x =
      W.eval out (mixedSlotInput (x (v 0)) (x (v 1)) (fun l => x (v l.succ.succ))) := by
  rw [mixedBoxComponent, Niltest.eval_linearPullbackHom, component_eval]
  apply congrArg (W.eval out)
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨l, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) l <;> rfl

theorem mixedBoxComponent_vertical (out : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedBoxComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedBoxComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

noncomputable def mixedKernelFactors (i j : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n) :
    Fin 2 → W.model.Niltest (fun _ : MixedBoxIndex n => 1) :=
  ![W.mixedBoxComponent i v,
    (W.mixedBoxComponent j (fun l => v (mixedExchangeCoordinate n l))).conjugate]

noncomputable def mixedKernelFrequencies : Fin 2 → (W.L →ₗ[ℚ] ℚ) :=
  ![W.vertical.frequency, -W.vertical.frequency]

theorem mixedKernelFactors_complexity (i j : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (a : Fin 2) : (W.mixedKernelFactors i j v a).ComplexityLE (p + 4) := by
  fin_cases a
  · exact W.component_complexity i
  · exact W.component_complexity j

theorem mixedKernelFactors_normBound (i j : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (a : Fin 2) : (W.mixedKernelFactors i j v a).normBound = 1 := by
  fin_cases a <;> rfl

theorem mixedKernelFactors_eval (i j : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (x : MixedBoxIndex n → ℤ) :
    (∏ a, (W.mixedKernelFactors i j v a).eval x) =
      W.mixedAntisymmetric i j (fun l => x (v l)) := by
  simp only [Fin.prod_univ_two, mixedKernelFactors, Matrix.cons_val_zero, Matrix.cons_val_one,
    Niltest.eval_conjugate, mixedBoxComponent_eval, mixedAntisymmetric]
  rfl

theorem mixedKernelFactors_vertical (i j : Fin W.outputDim) (v : Fin (n + 2) → MixedBoxIndex n)
    (a : Fin 2) (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedKernelFactors i j v a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.mixedKernelFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedKernelFactors i j v a).observable x := by
  fin_cases a
  · exact W.mixedBoxComponent_vertical i v z hz x
  · exact Niltest.conjugate_vertical _ _ (W.mixedBoxComponent_vertical j _) z hz x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

abbrev MixedBoxFactor (n : ℕ) := (Fin (n + 2) → Bool) × Fin 2

theorem mixedBoxFactor_card (n : ℕ) : Fintype.card (MixedBoxFactor n) = 2 ^ (n + 3) := by
  simp only [MixedBoxFactor, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  exact (pow_succ 2 (n + 2)).symm

def mixedBoxBudget (n : ℕ) (p : ℝ) : ℝ := p + 4 + ((2 ^ (n + 3) : ℕ) : ℝ)

theorem mixedBoxFactor_card_le_budget (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (Fintype.card (MixedBoxFactor n) : ℝ) ≤ mixedBoxBudget n p := by
  rw [mixedBoxFactor_card]
  dsimp only [mixedBoxBudget]
  linarith

def mixedBoxCorner {n : ℕ} (ω : Fin (n + 2) → Bool) : Fin (n + 2) → MixedBoxIndex n := fun i => (i, ω i)

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

noncomputable def mixedAntisymmetricBoxValue (i j : Fin W.outputDim) (x : MixedBoxIndex n → ℤ) : ℂ :=
  boxCornerProduct (W.mixedAntisymmetric i j) (fun a => x (a, false)) (fun a => x (a, true))

noncomputable def mixedAntisymmetricBoxFactors (i j : Fin W.outputDim) (a : MixedBoxFactor n) :
    W.model.Niltest (fun _ : MixedBoxIndex n => 1) :=
  let T := W.mixedKernelFactors i j (mixedBoxCorner a.1) a.2
  if booleanWeight a.1 % 2 = 0 then T else T.conjugate

noncomputable def mixedAntisymmetricBoxFrequencies (a : MixedBoxFactor n) : W.L →ₗ[ℚ] ℚ :=
  if booleanWeight a.1 % 2 = 0 then W.mixedKernelFrequencies a.2 else -W.mixedKernelFrequencies a.2

theorem mixedAntisymmetricBoxFactors_complexity (i j : Fin W.outputDim) (a : MixedBoxFactor n) :
    (W.mixedAntisymmetricBoxFactors i j a).ComplexityLE (mixedBoxBudget n p) := by
  have hbound : p + 4 ≤ mixedBoxBudget n p := le_add_of_nonneg_right (Nat.cast_nonneg _)
  unfold mixedAntisymmetricBoxFactors
  split <;> exact (W.mixedKernelFactors_complexity i j _ a.2).mono hbound

theorem mixedAntisymmetricBoxFactors_normBound (i j : Fin W.outputDim) (a : MixedBoxFactor n) :
    (W.mixedAntisymmetricBoxFactors i j a).normBound = 1 := by
  unfold mixedAntisymmetricBoxFactors
  split <;> exact W.mixedKernelFactors_normBound i j _ a.2

theorem mixedAntisymmetricBoxFactors_eval (i j : Fin W.outputDim) (x : MixedBoxIndex n → ℤ) :
    (∏ a, (W.mixedAntisymmetricBoxFactors i j a).eval x) = W.mixedAntisymmetricBoxValue i j x := by
  have hrow (ω : Fin (n + 2) → Bool) :
      (∏ b : Fin 2, (W.mixedAntisymmetricBoxFactors i j (ω, b)).eval x) =
        conjugationPower (booleanWeight ω) (W.mixedAntisymmetric i j (fun a => x (a, ω a))) := by
    rw [conjugationPower_eq_if_mod]
    by_cases hω : booleanWeight ω % 2 = 0
    · simpa only [mixedAntisymmetricBoxFactors, hω, ite_true, mixedBoxCorner] using
        W.mixedKernelFactors_eval i j (mixedBoxCorner ω) x
    · simpa only [mixedAntisymmetricBoxFactors, hω, ite_false, Niltest.eval_conjugate,
        star_prod, mixedBoxCorner] using
        congrArg star (W.mixedKernelFactors_eval i j (mixedBoxCorner ω) x)
  rw [Fintype.prod_prod_type]
  simp_rw [hrow]
  simp only [mixedAntisymmetricBoxValue, boxCornerProduct, boxCorner_pair]

theorem mixedAntisymmetricBoxValue_norm (i j : Fin W.outputDim) (x : MixedBoxIndex n → ℤ) :
    ‖W.mixedAntisymmetricBoxValue i j x‖ ≤ 1 := by
  rw [← W.mixedAntisymmetricBoxFactors_eval i j x, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro a _
  exact ((W.mixedAntisymmetricBoxFactors i j a).norm_eval_le x).trans_eq
    (by rw [W.mixedAntisymmetricBoxFactors_normBound i j a]; rfl)

theorem mixedAntisymmetricBoxFactors_vertical (i j : Fin W.outputDim) (a : MixedBoxFactor n)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedAntisymmetricBoxFactors i j a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.mixedAntisymmetricBoxFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedAntisymmetricBoxFactors i j a).observable x := by
  unfold mixedAntisymmetricBoxFactors mixedAntisymmetricBoxFrequencies
  split_ifs
  · exact W.mixedKernelFactors_vertical i j _ a.2 z hz x
  · exact Niltest.conjugate_vertical _ _ (W.mixedKernelFactors_vertical i j _ a.2) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]

noncomputable def mixedAntisymmetricBoxNiltest (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (pi (fun _ : MixedBoxFactor n => W.model)).Niltest (fun _ : MixedBoxIndex n => 1) :=
  piNiltest (fun _ : MixedBoxFactor n => W.model) (W.mixedAntisymmetricBoxFactors i j)
    (by dsimp only [mixedBoxBudget]; positivity)
    (mixedBoxFactor_card_le_budget n hp)
    (W.mixedAntisymmetricBoxFactors_complexity i j)

theorem mixedAntisymmetricBoxNiltest_complexity (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (W.mixedAntisymmetricBoxNiltest hp i j).ComplexityLE (productNiltestBudget (mixedBoxBudget n p)) :=
  piNiltest_complexity (fun _ : MixedBoxFactor n => W.model) (W.mixedAntisymmetricBoxFactors i j)
    (by dsimp only [mixedBoxBudget]; positivity)
    (mixedBoxFactor_card_le_budget n hp)
    (W.mixedAntisymmetricBoxFactors_complexity i j)

theorem mixedAntisymmetricBoxNiltest_eval (hp : 0 ≤ p) (i j : Fin W.outputDim)
    (x : MixedBoxIndex n → ℤ) :
    (W.mixedAntisymmetricBoxNiltest hp i j).eval x = W.mixedAntisymmetricBoxValue i j x := by
  rw [mixedAntisymmetricBoxNiltest, piNiltest_eval]
  exact W.mixedAntisymmetricBoxFactors_eval i j x

theorem mixedAntisymmetricBoxNiltest_vertical (hp : 0 ≤ p) (i j : Fin W.outputDim)
    (z : (pi (fun _ : MixedBoxFactor n => W.model)).RealGroup)
    (hz : z ∈ (pi (fun _ : MixedBoxFactor n => W.model)).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (pi (fun _ : MixedBoxFactor n => W.model)).Space) :
    (W.mixedAntisymmetricBoxNiltest hp i j).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency W.mixedAntisymmetricBoxFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (W.mixedAntisymmetricBoxNiltest hp i j).observable x :=
  piNiltest_vertical (fun _ : MixedBoxFactor n => W.model) (W.mixedAntisymmetricBoxFactors i j)
    W.mixedAntisymmetricBoxFrequencies (by dsimp only [mixedBoxBudget]; positivity)
    (mixedBoxFactor_card_le_budget n hp)
    (W.mixedAntisymmetricBoxFactors_complexity i j)
    (W.mixedAntisymmetricBoxFactors_vertical i j) z hz x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

theorem mixedAntisymmetricBoxValue_mean (N : ℕ) [NeZero N] (i j : Fin W.outputDim) :
    (𝔼 x ∈ integerBox (fun _ : MixedBoxIndex n => N), W.mixedAntisymmetricBoxValue i j x) =
      boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N => W.mixedAntisymmetric i j (fun a => (x a).val)) := by
  exact integerBox_cornerProduct_mean (n + 2) N (W.mixedAntisymmetric i j)

variable [TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]

theorem mixedAntisymmetricBoxNiltest_mean (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i j : Fin W.outputDim) :
    (𝔼 x ∈ integerBox (fun _ : MixedBoxIndex n => N), (W.mixedAntisymmetricBoxNiltest hp i j).eval x) =
      boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N => W.mixedAntisymmetric i j (fun a => (x a).val)) := by
  simp_rw [W.mixedAntisymmetricBoxNiltest_eval hp]
  exact W.mixedAntisymmetricBoxValue_mean N i j

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeMixedBoxFactorization {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  nonnegative : 0 ≤ p
  [topology : TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  [hausdorff : T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L))]
  basis : Basis (Fin (finrank ℚ (MixedBoxFactor n → W.L))) ℚ (MixedBoxFactor n → W.L)
  weight : Fin (finrank ℚ (MixedBoxFactor n → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : MixedBoxFactor n => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  height : ∀ i j, rationalLogHeight
    ((pi (fun _ : MixedBoxFactor n => W.model)).basis.repr (basis i) j) ≤ q
  factorization : (pi (fun _ : MixedBoxFactor n => W.model)).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency W.mixedAntisymmetricBoxFrequencies)
    (fun _ : MixedBoxIndex n => (N : ℝ))
    ((W.mixedAntisymmetricBoxNiltest nonnegative leftIndex rightIndex).symbol basis weight adapted) q

theorem exists_mixed_box_step_drop_indices (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        W.mixedAntisymmetric i j (fun a => (x a).val))).re →
      ∃ R : NativeMixedBoxFactorization W N ((p + C) ^ C),
        R.leftIndex = i ∧ R.rightIndex = j := by
  have hdegree : (∑ _ : MixedReplicatedIndex (n + 1), (1 : ℕ)) = n + 2 := by
    have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
    rw [Finset.sum_const, Finset.card_univ, hc]
    simp
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : MixedReplicatedIndex (n + 1), 1) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 4 + Polynomial.C (2 ^ (n + 3))
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + Polynomial.C (2 * (n + 2))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hN hbox
  let r := productNiltestBudget (mixedBoxBudget n p) + p + ((2 * (n + 2) : ℕ) : ℝ)
  have hprod : 0 ≤ productNiltestBudget (mixedBoxBudget n p) := by
    unfold productNiltestBudget productObservableLipBudget mixedBoxBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((2 * (n + 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpr : p ≤ r := by
    dsimp only [r]
    linarith only [hprod, hdim]
  have hdimr : ((2 * (n + 2) : ℕ) : ℝ) ≤ r := by dsimp only [r]; linarith only [hprod, hp]
  have hTr : productNiltestBudget (mixedBoxBudget n p) ≤ r := by
    dsimp only [r]
    linarith only [hp, hdim]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, R, r, mixedBoxBudget, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology
    (productFinBasis (fun _ : MixedBoxFactor n => W.model))
  let : TopologicalSpace (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L)) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L)) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L)) := htM
  let : T2Space (ℝ ⊗[ℚ] (MixedBoxFactor n → W.L)) := htT
  let D := pi (fun _ : MixedBoxFactor n => W.model)
  let T := W.mixedAntisymmetricBoxNiltest hp i j
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T
    ((W.mixedAntisymmetricBoxNiltest_complexity hp i j).mono hTr)
  have hbias : Real.exp (-r) ≤
      ‖𝔼 x ∈ translatedIntegerBox 0 (fun _ : MixedBoxIndex n => N), T.eval x‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : MixedBoxIndex n => N) =
        integerBox (fun _ : MixedBoxIndex n => N) := by
      ext x
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero, show T = W.mixedAntisymmetricBoxNiltest hp i j from rfl,
      W.mixedAntisymmetricBoxNiltest_mean]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hbox.trans (Complex.re_le_norm _))
  have hf := hconstruct (piFrequency W.mixedAntisymmetricBoxFrequencies)
    (W.mixedAntisymmetricBoxNiltest_vertical hp i j) 0 (fun _ : MixedBoxIndex n => N)
    (fun _ => NeZero.pos N) (by simpa [MixedBoxIndex, Nat.mul_comm] using hdimr)
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

end Erdos3

end

end OAI
