import OAI.Analysis.Pureness.Comparison.HereditaryApproximation
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace OAI
open scoped ComplexOrder
open Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma TracialState.re_apply_mul_contraction_le (τ : TracialState A)
    {e x : A} (he : 0 ≤ e) (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1) :
    (τ.toPositiveLinearMap (e * x)).re ≤ (τ.toPositiveLinearMap e).re := by
  let t := CFC.sqrt e
  have ht : IsSelfAdjoint t := (CFC.sqrt_nonneg e).isSelfAdjoint
  have htt : t * t = e := CFC.sqrt_mul_sqrt_self e he
  have hx1 : x ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg x hx).mp hxn
  have hle : t * x * t ≤ e := by
    have h := star_left_conjugate_le_conjugate hx1 t
    simpa only [ht.star_eq, mul_one, htt] using h
  have heq : τ.toPositiveLinearMap (e * x) = τ.toPositiveLinearMap (t * x * t) := by
    rw [← htt]
    simpa only [mul_assoc] using τ.tracial t (t * x)
  rw [heq]
  exact (Complex.le_def.mp (τ.toPositiveLinearMap.monotone hle)).1

theorem TracialState.hereditary_contraction_trace_le (τ : TracialState A)
    {b x : A} (hb : 0 ≤ b) (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1)
    (hxm : x ∈ hereditaryCorner b hb) :
    (τ.toPositiveLinearMap x).re ≤ (τ.spectralSupportMass b hb).toReal := by
  have hlim := ((map_continuous τ.toPositiveLinearMap).tendsto x).comp
    (supportApprox_mul_tendsto hb hxm)
  apply le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hlim)
  apply Eventually.of_forall
  intro n
  exact (τ.re_apply_mul_contraction_le (supportApprox_nonneg b n) hx hxn).trans
    (τ.supportApprox_trace_le hb n)

theorem TracialState.hereditary_support_mass_le (τ : TracialState A)
    {b c : A} (hb : 0 ≤ b) (hc : 0 ≤ c) (hcb : c ∈ hereditaryCorner b hb) :
    (τ.spectralSupportMass c hc).toReal ≤ (τ.spectralSupportMass b hb).toReal := by
  apply le_of_tendsto (τ.supportApprox_trace_tendsto hc)
  apply Eventually.of_forall
  intro n
  exact τ.hereditary_contraction_trace_le hb (supportApprox_nonneg c n)
    (supportApprox_norm_le_one c n)
    (hereditaryCorner_le_of_mem hb hc hcb (supportApprox_mem hc n))

theorem exists_linking_support_mass_bound [IsSimpleCStarAlgebra A]
    {c d : A} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcn : c ≠ 0) (hdn : d ≠ 0) :
    ∃ e : A, ∃ he : 0 ≤ e, e ≠ 0 ∧ e ∈ hereditaryCorner d hd ∧
      ∀ τ : TracialState A,
        (τ.spectralSupportMass e he).toReal ≤ (τ.spectralSupportMass c hc).toReal ∧
        (τ.spectralSupportMass e he).toReal ≤ (τ.spectralSupportMass d hd).toReal := by
  obtain ⟨z, hzn, hzn', hzn'', hz, hz', hzd, hzc, ht⟩ :=
    exists_hereditary_linking_squares hc hd hcn hdn
  refine ⟨star z * z, hz, hzn', hzd, fun τ => ⟨?_, ?_⟩⟩
  · rw [τ.linking_support_mass]
    exact τ.hereditary_support_mass_le hc hz' hzc
  · exact τ.hereditary_support_mass_le hd hz hzd
end CuntzComparison

end OAI
