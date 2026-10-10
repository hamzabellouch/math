import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealInnerAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarAutomorphisms

namespace OAI

/-! # One ideal Haar measure for both boxes and ambient conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

section Haar

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)

include hExp in
theorem exists_coneIdeal_inner_invariant_haar
    (haar : NilpotentExponentialHaarInput E Q)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ (μ : Measure Q) (hbij : Function.Bijective Exp), μ.IsHaarMeasure ∧
      (∀ x : cartanRootIdeal H,
        MeasurePreserving (exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C x)) μ μ) ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r R : ℝ), 0 ≤ R →
        μ (M.coneIdealBox C (Exp ∘ e) s β r R) =
          ENNReal.ofReal |(columnBasisMatrix
            (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (M.coneWordIdeal C) := by
  have hnil := e.nilpotent_iff_equiv_nilpotent.mp (M.coneIdeal_nilpotent C)
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  have hbij : Function.Bijective Exp := by
    have heq : Exp = chart := funext fun x => (hchart x).symm
    rw [heq]
    exact chart.bijective
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  have hμ : μ.IsHaarMeasure := by
    have hf : ((Exp ∘ e) ∘ b₀.equivFun.symm) =
        Exp ∘ (b₀.map e.toLinearEquiv).equivFun.symm := by
      funext t
      rw [Basis.map_equivFun]
      rfl
    change (Measure.map _ volume).IsHaarMeasure
    rw [hf]
    exact hhaar _ _
  refine ⟨μ, hbij, hμ, ?_, ?_⟩
  · intro x
    exact exponentialConjugate_measurePreserving e Exp hbij chart hchart b₀
      (M.coneIdealInnerAutomorphism C x) (M.coneIdealInnerAutomorphism_det C x)
  · intro s β r R hR
    exact exponentialCoordinate_weighted_box_measure e Exp chart hchart b₀
      (M.coneMixedVector C) (M.coneIdealWordList C)
      (fun w => M.coneIdealWordCost C s w) β r R hR

end Haar

local instance innerHaarNormedAddCommGroup : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance innerHaarNormedSpace : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

variable {G A : Type*} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (ExpN : cartanRootIdeal H → G) (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A)
  (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))

include hρ hmatch in
theorem coneIdealInnerAutomorphism_exp_conjugation (x : cartanRootIdeal H)
    (v : M.coneWordIdeal C) :
    ExpN (M.coneIdealInnerAutomorphism C x v : cartanRootIdeal H) =
      ExpN x * ExpN (v : cartanRootIdeal H) * (ExpN x)⁻¹ := by
  let D := toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) x
  have hD : D ^ M.bound = 0 := by
    apply LinearMap.ext
    intro y
    rw [Module.End.pow_apply, LinearMap.zero_apply]
    have hy := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) x y M.bound
    rw [M.bound_zero] at hy
    exact hy
  rw [M.coneIdealInnerAutomorphism_apply]
  have hm := finiteEndFlow_map (M.coneWordIdeal C).incl.toLinearMap
    (M.coneIdealInnerDerivation C x).toLinearMap D (fun _ => rfl) M.bound 1 v
  calc
    _ = ExpN (finiteEndFlow D M.bound 1 (v : cartanRootIdeal H)) := congrArg ExpN hm
    _ = _ := by
      rw [finiteEndFlow_eq_exp D hD]
      have hh := exp_ad_eq_group_conjugation ExpN j ρ hρ hmatch x v 1
      rw [one_smul, one_smul] at hh
      rw [one_smul]
      exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
