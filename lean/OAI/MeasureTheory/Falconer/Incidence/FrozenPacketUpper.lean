import OAI.MeasureTheory.Falconer.Incidence.VariableBaselineIncidence
import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! The fine packet sizes after dyadic freezing are bounded by the
original total fine-tube count and the geometric coarse incidence estimate. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_packet_card_upper (N k : ℕ) {s t K m M B : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 ≤ M)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hband : ∀ a ∈ P.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1))
    (htotal : (∑ a ∈ P.biUnion T, ((G a).card:ℝ)) ≤ B) :
    ∀ a ∈ P.biUnion T, ((G a).card:ℝ) ≤
      2*B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 := by
  have hb := packet_size_from_variable_incidence N hs hst hK hm.le hM
    (show 0 ≤ (2:ℝ)^k by positivity) P T hP hPchart hPball hT (fun a => (G a).card)
    (fun a ha => by exact_mod_cast (hband a ha).1) htotal
  intro a ha
  have hu : ((G a).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband a ha).2
  have hk : (2:ℝ)^k ≤ B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 :=
    (le_div_iff₀ (sq_pos_of_pos hm)).2 hb
  calc
    _ ≤ 2*(2:ℝ)^k := by simpa only [pow_succ,mul_comm] using hu.le
    _ ≤ 2*(B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2) :=
      mul_le_mul_of_nonneg_left hk (by norm_num)
    _ = _ := by ring

theorem frozen_packet_upper_power (N : ℕ) {κ s t K m M B E Δ : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hK : 0 ≤ K) (hKup : K ≤ E) (_hm : 0 < m) (hM : 0 ≤ M)
    (hMup : M ≤ E/(1/(2:ℝ)^N)^s) (hmlo : 1/(E*(1/(2:ℝ)^N)^s) ≤ m)
    (_hB : 0 ≤ B) (hBup : B ≤ E/(Δ^s)^4)
    (hE : 1 ≤ E) (hΔ : 0 < Δ) (hρΔ : 1/(2:ℝ)^N ≤ Δ) :
    2*B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 ≤
      (160*(1+projectionGapConstant κ))*E^6/(Δ^s)^2 := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hρ : 0 < 1/(2:ℝ)^N := by positivity
  have hρs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hρ _
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hscale : (1/(2:ℝ)^N)^s ≤ Δ^s := Real.rpow_le_rpow hρ.le hρΔ hs
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hH := projectionGapConstant_pos hκ
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs1
  have hA : K*(80*(1/(2:ℝ)^N))^s*M ≤ 80*E^2 := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
    calc
      _ ≤ E*(80*(1/(2:ℝ)^N)^s)*(E/(1/(2:ℝ)^N)^s) := by gcongr
      _ = _ := by field_simp
  have hpot : 1+K*planarPotentialConstant s t ≤ (1+projectionGapConstant κ)*E := by
    calc
      _ ≤ 1+E*projectionGapConstant κ := by
        gcongr
        exact planarPotentialConstant_gap hκ hs1 hgap
      _ ≤ _ := by nlinarith only [hE]
  calc
    _ ≤ 2*(E/(Δ^s)^4)*((80*E^2)*((1+projectionGapConstant κ)*E))/
        (1/(E*(1/(2:ℝ)^N)^s))^2 := by gcongr
    _ = (160*(1+projectionGapConstant κ))*E^6*((1/(2:ℝ)^N)^s)^2/(Δ^s)^4 := by field_simp; ring
    _ ≤ (160*(1+projectionGapConstant κ))*E^6*(Δ^s)^2/(Δ^s)^4 := by gcongr
    _ = _ := by field_simp

end Falconer

end OAI
