import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
import OAI.Combinatorics.Progressions.Estimates.QuarticAntisymmetricTransfer

namespace OAI

section

namespace Erdos3

abbrev QuarticBoxIndex := Fin 4 × Bool

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticBoxComponent (out : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex) :
    W.model.Niltest (fun _ : QuarticBoxIndex => 1) :=
  (W.component out).affinePullback
    (fun j a => if a = (if j.1 = 0 then v 0 else if j.2.val = 0 then v 1
      else if j.2.val = 1 then v 2 else v 3) then 1 else 0) (fun _ => 0)

theorem quarticBoxComponent_eval (out : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (n : QuarticBoxIndex → ℤ) :
    (W.quarticBoxComponent out v).eval n =
      W.eval out (quarticInput (n (v 0)) ![n (v 1), n (v 2), n (v 3)]) := by
  rw [quarticBoxComponent, Niltest.eval_affinePullback, component_eval]
  apply congrArg (W.eval out)
  funext j
  rcases j with ⟨j, a⟩
  fin_cases j <;> fin_cases a <;>
    simp [integerAffineMap, quarticInput, ite_mul]

theorem quarticBoxComponent_vertical (out : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.quarticBoxComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.quarticBoxComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

noncomputable def quarticKernelFactors (i j : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex) :
    Fin 2 → W.model.Niltest (fun _ : QuarticBoxIndex => 1) :=
  ![W.quarticBoxComponent i v, (W.quarticBoxComponent j ![v 1, v 0, v 2, v 3]).conjugate]

noncomputable def quarticKernelFrequencies : Fin 2 → (W.L →ₗ[ℚ] ℚ) :=
  ![W.vertical.frequency, -W.vertical.frequency]

theorem quarticKernelFactors_complexity (i j : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (a : Fin 2) : (W.quarticKernelFactors i j v a).ComplexityLE (p + 32) := by
  have hi := (W.component_complexity i).mono (by linarith : p + 4 ≤ p + 32)
  have hj := (W.component_complexity j).mono (by linarith : p + 4 ≤ p + 32)
  fin_cases a
  · exact hi
  · exact hj

theorem quarticKernelFactors_normBound (i j : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (a : Fin 2) : (W.quarticKernelFactors i j v a).normBound = 1 := by
  fin_cases a <;> rfl

theorem quarticKernelFactors_eval (i j : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (n : QuarticBoxIndex → ℤ) :
    (∏ a, (W.quarticKernelFactors i j v a).eval n) =
      W.quarticAntisymmetric i j (fun a => n (v a)) := by
  simp [quarticKernelFactors, Fin.prod_univ_two, quarticBoxComponent_eval, quarticAntisymmetric]

theorem quarticKernelFactors_vertical (i j : Fin W.outputDim) (v : Fin 4 → QuarticBoxIndex)
    (a : Fin 2) (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.quarticKernelFactors i j v a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.quarticKernelFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (W.quarticKernelFactors i j v a).observable x := by
  fin_cases a
  · exact W.quarticBoxComponent_vertical i v z hz x
  · exact Niltest.conjugate_vertical _ _ (W.quarticBoxComponent_vertical j _) z hz x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

abbrev QuarticBoxFactor := (Fin 4 → Bool) × Fin 2

theorem quarticBoxFactor_card : Fintype.card QuarticBoxFactor = 32 := by decide

def quarticBoxCorner (ω : Fin 4 → Bool) : Fin 4 → QuarticBoxIndex := fun i => (i, ω i)

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticAntisymmetricBoxValue (i j : Fin W.outputDim) (n : QuarticBoxIndex → ℤ) : ℂ :=
  boxCornerProduct (W.quarticAntisymmetric i j) (fun a => n (a, false)) (fun a => n (a, true))

noncomputable def quarticAntisymmetricBoxFactors (i j : Fin W.outputDim) (a : QuarticBoxFactor) :
    W.model.Niltest (fun _ : QuarticBoxIndex => 1) :=
  let T := W.quarticKernelFactors i j (quarticBoxCorner a.1) a.2
  if booleanWeight a.1 % 2 = 0 then T else T.conjugate

noncomputable def quarticAntisymmetricBoxFrequencies (a : QuarticBoxFactor) : W.L →ₗ[ℚ] ℚ :=
  if booleanWeight a.1 % 2 = 0 then W.quarticKernelFrequencies a.2 else -W.quarticKernelFrequencies a.2

theorem quarticAntisymmetricBoxFactors_complexity (i j : Fin W.outputDim) (a : QuarticBoxFactor) :
    (W.quarticAntisymmetricBoxFactors i j a).ComplexityLE (p + 32) := by
  unfold quarticAntisymmetricBoxFactors
  split <;> exact W.quarticKernelFactors_complexity i j _ a.2

theorem quarticAntisymmetricBoxFactors_normBound (i j : Fin W.outputDim) (a : QuarticBoxFactor) :
    (W.quarticAntisymmetricBoxFactors i j a).normBound = 1 := by
  unfold quarticAntisymmetricBoxFactors
  split <;> exact W.quarticKernelFactors_normBound i j _ a.2

theorem quarticAntisymmetricBoxFactors_eval (i j : Fin W.outputDim) (n : QuarticBoxIndex → ℤ) :
    (∏ a, (W.quarticAntisymmetricBoxFactors i j a).eval n) = W.quarticAntisymmetricBoxValue i j n := by
  have hrow (ω : Fin 4 → Bool) :
      (∏ b : Fin 2, (W.quarticAntisymmetricBoxFactors i j (ω, b)).eval n) =
        conjugationPower (booleanWeight ω) (W.quarticAntisymmetric i j (fun a => n (a, ω a))) := by
    rw [conjugationPower_eq_if_mod]
    by_cases hω : booleanWeight ω % 2 = 0
    · simpa only [quarticAntisymmetricBoxFactors, hω, ite_true, quarticBoxCorner] using
        W.quarticKernelFactors_eval i j (quarticBoxCorner ω) n
    · simpa only [quarticAntisymmetricBoxFactors, hω, ite_false, Niltest.eval_conjugate,
        star_prod, quarticBoxCorner] using
        congrArg star (W.quarticKernelFactors_eval i j (quarticBoxCorner ω) n)
  rw [Fintype.prod_prod_type]
  simp_rw [hrow]
  simp only [quarticAntisymmetricBoxValue, boxCornerProduct, boxCorner_pair]

theorem quarticAntisymmetricBoxValue_norm (i j : Fin W.outputDim) (n : QuarticBoxIndex → ℤ) :
    ‖W.quarticAntisymmetricBoxValue i j n‖ ≤ 1 := by
  rw [← W.quarticAntisymmetricBoxFactors_eval i j n, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro a _
  exact ((W.quarticAntisymmetricBoxFactors i j a).norm_eval_le n).trans_eq
    (by rw [W.quarticAntisymmetricBoxFactors_normBound i j a]; rfl)

theorem quarticAntisymmetricBoxFactors_vertical (i j : Fin W.outputDim) (a : QuarticBoxFactor)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.quarticAntisymmetricBoxFactors i j a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.quarticAntisymmetricBoxFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (W.quarticAntisymmetricBoxFactors i j a).observable x := by
  unfold quarticAntisymmetricBoxFactors quarticAntisymmetricBoxFrequencies
  split_ifs
  · exact W.quarticKernelFactors_vertical i j _ a.2 z hz x
  · exact Niltest.conjugate_vertical _ _ (W.quarticKernelFactors_vertical i j _ a.2) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]

noncomputable def quarticAntisymmetricBoxNiltest (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (pi (fun _ : QuarticBoxFactor => W.model)).Niltest (fun _ : QuarticBoxIndex => 1) :=
  piNiltest (fun _ : QuarticBoxFactor => W.model) (W.quarticAntisymmetricBoxFactors i j)
    (by linarith)
    (by simpa only [quarticBoxFactor_card, Nat.cast_ofNat] using (show (32 : ℝ) ≤ p + 32 by linarith))
    (W.quarticAntisymmetricBoxFactors_complexity i j)

theorem quarticAntisymmetricBoxNiltest_complexity (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (W.quarticAntisymmetricBoxNiltest hp i j).ComplexityLE (productNiltestBudget (p + 32)) :=
  piNiltest_complexity (fun _ : QuarticBoxFactor => W.model) (W.quarticAntisymmetricBoxFactors i j)
    (by linarith)
    (by simpa only [quarticBoxFactor_card, Nat.cast_ofNat] using (show (32 : ℝ) ≤ p + 32 by linarith))
    (W.quarticAntisymmetricBoxFactors_complexity i j)

theorem quarticAntisymmetricBoxNiltest_eval (hp : 0 ≤ p) (i j : Fin W.outputDim)
    (n : QuarticBoxIndex → ℤ) :
    (W.quarticAntisymmetricBoxNiltest hp i j).eval n = W.quarticAntisymmetricBoxValue i j n := by
  rw [quarticAntisymmetricBoxNiltest, piNiltest_eval]
  exact W.quarticAntisymmetricBoxFactors_eval i j n

theorem quarticAntisymmetricBoxNiltest_vertical (hp : 0 ≤ p) (i j : Fin W.outputDim)
    (z : (pi (fun _ : QuarticBoxFactor => W.model)).RealGroup)
    (hz : z ∈ (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1))
    (x : (pi (fun _ : QuarticBoxFactor => W.model)).Space) :
    (W.quarticAntisymmetricBoxNiltest hp i j).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency W.quarticAntisymmetricBoxFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (W.quarticAntisymmetricBoxNiltest hp i j).observable x :=
  piNiltest_vertical (fun _ : QuarticBoxFactor => W.model) (W.quarticAntisymmetricBoxFactors i j)
    W.quarticAntisymmetricBoxFrequencies (by linarith)
    (by simpa only [quarticBoxFactor_card, Nat.cast_ofNat] using (show (32 : ℝ) ≤ p + 32 by linarith))
    (W.quarticAntisymmetricBoxFactors_complexity i j)
    (W.quarticAntisymmetricBoxFactors_vertical i j) z hz x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

theorem quarticAntisymmetricBoxValue_mean (N : ℕ) [NeZero N] (i j : Fin W.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : QuarticBoxIndex => N), W.quarticAntisymmetricBoxValue i j n) =
      boxPhaseMoment 4 (fun x : Fin 4 → ZMod N => W.quarticAntisymmetric i j (fun a => (x a).val)) := by
  exact integerBox_cornerProduct_mean 4 N (W.quarticAntisymmetric i j)

variable [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]

theorem quarticAntisymmetricBoxNiltest_mean (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i j : Fin W.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : QuarticBoxIndex => N), (W.quarticAntisymmetricBoxNiltest hp i j).eval n) =
      boxPhaseMoment 4 (fun x : Fin 4 → ZMod N => W.quarticAntisymmetric i j (fun a => (x a).val)) := by
  simp_rw [W.quarticAntisymmetricBoxNiltest_eval hp]
  exact W.quarticAntisymmetricBoxValue_mean N i j

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeQuarticBoxFactorization {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  nonnegative : 0 ≤ p
  [topology : TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [hausdorff : T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  basis : Basis (Fin (finrank ℚ (QuarticBoxFactor → W.L))) ℚ (QuarticBoxFactor → W.L)
  weight : Fin (finrank ℚ (QuarticBoxFactor → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : QuarticBoxFactor => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  height : ∀ i j, rationalLogHeight
    ((pi (fun _ : QuarticBoxFactor => W.model)).basis.repr (basis i) j) ≤ q
  factorization : (pi (fun _ : QuarticBoxFactor => W.model)).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency W.quarticAntisymmetricBoxFrequencies)
    (fun _ : QuarticBoxIndex => (N : ℝ))
    ((W.quarticAntisymmetricBoxNiltest nonnegative leftIndex rightIndex).symbol basis weight adapted) q

theorem exists_quartic_box_step_drop_indices :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
        W.quarticAntisymmetric i j (fun a => (x a).val))).re →
      ∃ R : NativeQuarticBoxFactorization W N ((p + C) ^ C),
        R.leftIndex = i ∧ R.rightIndex = j := by
  have hdegree : (∑ _ : QuarticReplicatedIndex, (1 : ℕ)) = 4 := by
    have hc : Fintype.card QuarticReplicatedIndex = 4 := replicatedMixed_card 3
    rw [Finset.sum_const, Finset.card_univ, hc]
    rfl
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : QuarticReplicatedIndex, 1) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hN hbox
  let r := productNiltestBudget (p + 32) + p + 8
  have hprod : 0 ≤ productNiltestBudget (p + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith only [hprod]
  have h8r : 8 ≤ r := by dsimp only [r]; linarith only [hprod, hp]
  have hTr : productNiltestBudget (p + 32) ≤ r := by dsimp only [r]; linarith only [hp]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, R, r, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology
    (productFinBasis (fun _ : QuarticBoxFactor => W.model))
  let : TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L)) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L)) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L)) := htM
  let : T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L)) := htT
  let D := pi (fun _ : QuarticBoxFactor => W.model)
  let T := W.quarticAntisymmetricBoxNiltest hp i j
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T
    ((W.quarticAntisymmetricBoxNiltest_complexity hp i j).mono hTr)
  have hbias : Real.exp (-r) ≤
      ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : QuarticBoxIndex => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : QuarticBoxIndex => N) =
        integerBox (fun _ : QuarticBoxIndex => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero, show T = W.quarticAntisymmetricBoxNiltest hp i j from rfl,
      W.quarticAntisymmetricBoxNiltest_mean]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hbox.trans (Complex.re_le_norm _))
  have hf := hconstruct (piFrequency W.quarticAntisymmetricBoxFrequencies)
    (W.quarticAntisymmetricBoxNiltest_vertical hp i j) 0 (fun _ : QuarticBoxIndex => N)
    (fun _ => NeZero.pos N) (by simpa [QuarticBoxIndex] using h8r)
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
