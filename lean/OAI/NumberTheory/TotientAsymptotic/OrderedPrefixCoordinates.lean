import OAI.NumberTheory.TotientAsymptotic.OrderedPrefixLower
import OAI.NumberTheory.TotientAsymptotic.StrictPrefixContraction
import OAI.NumberTheory.TotientAsymptotic.StrictContractionCost

namespace OAI

/-! The ordered positive-volume family retains a geometric lower envelope. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma orderedSlackRegion_coordinate_lower {N : ℕ} {B t : ℝ}
    {u : Fin N → ℝ} (hu : u ∈ orderedSlackRegion N B t) (i : Fin N) :
    t*g (N-i.val) ≤ u i := by
  let v := u-renewalBackground N t
  have hv : v ∈ prefixRegion N (∑ j : Fin N,a (j.val+1)*v j) 0 0 := by
    refine ⟨?_,by simp⟩
    intro j
    change 0 ≤ prefixLinear N (u-renewalBackground N t) j
    rw [map_sub,Pi.sub_apply,renewalBackground_slack]
    exact sub_nonneg.mpr (hu.2.2 j)
  have hh := prefixRegion_coordinate_nonneg hv i
  change 0 ≤ u i-t*g (N-i.val) at hh
  linarith only [hh]

theorem contracted_ordered_coordinate_lower : ∃ c : ℝ,0 < c ∧
    ∀ {m N : ℕ},N ≤ m → ∀ {B t : ℝ},0 ≤ t →
      ∀ {u : Fin N → ℝ},u ∈ orderedSlackRegion N B t → ∀ i : Fin N,
        c*t*(rho^(N-i.val))⁻¹ ≤
          simplexScale (enlargementScale (fun r => 1+rowContractionError (m-r))) u i := by
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  let M := Real.exp rowContractionCost
  have hM : 0 < M := Real.exp_pos _
  refine ⟨c/M,div_pos hc hM,?_⟩
  intro m N hNm B t ht u hu i
  let κ : Fin N → ℝ := enlargementScale (fun r => 1+rowContractionError (m-r))
  have hkpos : 0 < κ i := enlargementScale_pos
    (fun r => by linarith only [rowContractionError_nonneg (m-r)]) i
  have hkM : κ i ≤ M := row_contraction_coordinate hNm i
  have hu0 := prefixRegion_coordinate_nonneg hu.1 i
  have huM := div_le_div_of_nonneg_right (orderedSlackRegion_coordinate_lower hu i) hM.le
  have hrenew := mul_le_mul_of_nonneg_left (hg (N-i.val)) ht
  have hlower := div_le_div_of_nonneg_right hrenew hM.le
  calc
    _ = (t*(c*(rho^(N-i.val))⁻¹))/M := by ring
    _ ≤ (t*g (N-i.val))/M := hlower
    _ ≤ u i/M := huM
    _ ≤ u i/κ i := div_le_div_of_nonneg_left hu0 hkpos hkM
    _ = _ := (simplexScale_apply _ _ _).symm

end TotientAsymptotic

end

end OAI
