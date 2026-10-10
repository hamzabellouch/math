import OAI.Analysis.Pureness.Comparison.SpectralMeasure
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

namespace OAI
open MeasureTheory Set
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem TracialState.spectralMeasure_cfc (τ : TracialState A) (a : A)
    (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f) :
    τ.spectralMeasure (cfc f a) (cfc_predicate f a) =
      (τ.spectralMeasure a ha).map f := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [τ.integral_spectralMeasure _ _ g g.continuous,
    integral_map (φ := f) (f := fun t : ℝ => g t) hf.aemeasurable (by fun_prop),
    τ.integral_spectralMeasure a ha (fun t => g (f t)) (g.continuous.comp hf)]
  rw [cfc_comp' g f a g.continuous.continuousOn hf.continuousOn]

noncomputable def positiveCut (a : A) (s : ℝ) : A :=
  cfc (fun t : ℝ => max (t - s) 0) a

lemma positiveCut_nonneg (a : A) (s : ℝ) : 0 ≤ positiveCut a s := by
  apply cfc_nonneg
  intro t ht
  exact le_max_right _ _

theorem TracialState.positiveCut_support_mass (τ : TracialState A) (a : A)
    (ha : IsSelfAdjoint a) (s : ℝ) :
    τ.spectralSupportMass (positiveCut a s) (positiveCut_nonneg a s) =
      τ.spectralMeasure a ha (Ioi s) := by
  unfold TracialState.spectralSupportMass positiveCut
  rw [τ.spectralMeasure_cfc a ha _ (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext t
  simp only [mem_preimage, mem_Ioi, lt_max_iff, lt_self_iff_false, or_false, sub_pos]

theorem TracialState.smul_support_mass (τ : TracialState A) {a : A} (ha : 0 ≤ a)
    {r : ℝ} (hr : 0 < r) :
    τ.spectralSupportMass (r • a) (smul_nonneg hr.le ha) = τ.spectralSupportMass a ha := by
  have heq : cfc (fun t : ℝ => r * t) a = r • a := by
    simpa only [smul_eq_mul] using cfc_smul_id (R := ℝ) r a
  have ht := τ.spectralMeasure_cfc a ha.isSelfAdjoint (fun t : ℝ => r * t) (by fun_prop)
  simp only [heq] at ht
  unfold TracialState.spectralSupportMass
  rw [ht,
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext t
  simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hr]

theorem TracialState.linking_cut_support_mass (τ : TracialState A) (z : A) (s : ℝ) :
    τ.spectralSupportMass (positiveCut (star z * z) s) (positiveCut_nonneg _ s) =
      τ.spectralSupportMass (positiveCut (z * star z) s) (positiveCut_nonneg _ s) := by
  rw [τ.positiveCut_support_mass _ (star_mul_self_nonneg z).isSelfAdjoint,
    τ.positiveCut_support_mass _ (mul_star_self_nonneg z).isSelfAdjoint,
    τ.linking_spectralMeasure]
end CuntzComparison

end OAI
