import OAI.Analysis.HenonEmden.PressureEstimate

namespace OAI

section RelativePressure

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma pressure_relative {n : ℕ} (hn : 3 ≤ n) {p q A B ε : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
      (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
        radialPressure (source u q B) (source v p A) ≤
        ε*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+C := by
  let G := pressureGeomCoefficient n
  have hG : 0 ≤ G := pressureGeomCoefficient_nonneg (by omega)
  let κ := min 1 (ε/(3*(G+1)))
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hGκ : G*κ ≤ ε/3 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 3*(G+1))).mp (min_le_right 1 (ε/(3*(G+1))))
    change κ*(3*(G+1)) ≤ ε at hh
    nlinarith
  let S := pressureSmallCoefficient n p q A B κ
  have hS : 0 ≤ S := pressureSmallCoefficient_nonneg n p q A B hκ.le
  let δ := min (1/4) (ε/(3*(S+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hSδ : S*δ ≤ ε/3 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 3*(S+1))).mp (min_le_right (1/4) (ε/(3*(S+1))))
    change δ*(3*(S+1)) ≤ ε at hh
    nlinarith
  let H := pressureHighCoefficient n p q A B κ δ
  let P := max 1 (3*H/ε)
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hHP : H/P ≤ ε/3 := by
    apply (div_le_iff₀ hP).mpr
    have hh := (div_le_iff₀ hε).mp (le_max_right 1 (3*H/ε))
    change 3*H ≤ P*ε at hh
    nlinarith
  have hc : G*κ+S*δ+H/P ≤ ε := by linarith
  refine ⟨pressureConstant n p q A B κ δ P,pressureConstant_nonneg n p q A B hκ.le hδ.le hP.le,?_⟩
  intro u v h
  have he := h.pressure_estimate hn hp hq hκ hκ1 hδ hδ1 hP
  have hE : 0 ≤ weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A :=
    add_nonneg (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_u x).le))
      (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le))
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hc hE) le_rfl)

end HenonLaneEmden
end
end RelativePressure

end OAI
