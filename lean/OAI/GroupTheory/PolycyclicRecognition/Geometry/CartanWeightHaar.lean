import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanJacobian
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarAutomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarMeasureTransfer
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialAutomorphismTopology

namespace OAI

/-! # Haar preservation by the source probe dilation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (e : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput E N)
  (haar : NilpotentExponentialHaarInput E N)

include hunimod haar M hExp hbij dynkin

/-- The actual scalar dilation preserves any chosen Haar normalization.
Thus moving the contact pivot costs no probe volume. -/
theorem weightDilation_preserves_haar (μ : Measure N) [μ.IsHaarMeasure] (h : H) :
    MeasurePreserving
      (integrateNilpotentLieEquiv e Exp hbij dynkin hExp M.bound_zero
        (cartanIdealWeightDilation T H h)) μ μ := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  let b := finBasis ℝ (cartanRootIdeal H)
  let coordinates := (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : LocallyCompactSpace N := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := coordinates.symm.secondCountableTopology
  obtain ⟨ν, hν, hinv⟩ := exists_haar_preserved_by_exponentialConjugate
    e Exp hbij chart hchart b haar hExp hnil
  let : ν.IsHaarMeasure := hν
  apply measurePreserving_of_haarMeasure ν μ _
  exact hinv (cartanIdealWeightDilation T H h) (M.det_idealWeightDilation_eq_one T hunimod h)

/-- Source dilations with the same exponential formula preserve the same
Haar volume. -/
theorem weightDilation_preserves_haar_of_exp_action
    (μ : Measure N) [μ.IsHaarMeasure] (h : H) (S : N → N)
    (hS : ∀ v, S (Exp (e v)) = Exp (e (cartanIdealWeightDilation T H h v))) :
    MeasurePreserving S μ μ := by
  have he : S = integrateNilpotentLieEquiv e Exp hbij dynkin hExp M.bound_zero
      (cartanIdealWeightDilation T H h) := by
    funext g
    obtain ⟨v, rfl⟩ := (hbij.comp e.bijective).surjective g
    change S (Exp (e v)) = integrateNilpotentLieEquiv e Exp hbij dynkin hExp
      M.bound_zero (cartanIdealWeightDilation T H h) (Exp (e v))
    exact (hS v).trans (integrateNilpotentLieEquiv_apply_exp e Exp hbij dynkin hExp
      M.bound_zero (cartanIdealWeightDilation T H h) v).symm
  rw [he]
  exact M.weightDilation_preserves_haar T hunimod e Exp hExp hbij dynkin haar μ h

end PolycyclicRecognition.CartanWordModel

end

end OAI
