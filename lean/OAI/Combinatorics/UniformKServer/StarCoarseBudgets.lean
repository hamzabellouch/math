import Mathlib
import OAI.Combinatorics.UniformKServer.StarBudget
import OAI.Combinatorics.UniformKServer.StarEnergy

namespace OAI

                                        
section

/-! Fixed absolute coarse-charge constants. They carry no factor of ell. -/
noncomputable section
namespace UniformKServer.StarCoarseBudgets
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem child_allowance (d : Data Ω ι k) (H : ℕ) :
    (∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k ≤ energy d H :=
  add_le_add (child_drift d H) (allowance_bounds ι k).2.2.2

theorem parent_allowance (d : Data Ω ι k) (H : ℕ) :
    totalDrift (parentInput d) H+k ≤ energy d H :=
  add_le_add (parent_drift d H) (allowance_bounds ι k).2.1

theorem core_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (coreChanges d) ≤ 36864*energy d H := by
  have h := sum_le_sum (s:=univ) fun i _ => coreChange_budget (input d i) d.weight
    (fun ω => (d.positive ω).le) (fun _ => rfl) H
  simp only [Fintype.card_fin] at h
  change integral d H (fun t ω => ∑ i, coreChange (input d i) t ω) ≤ _
  rw [integral_sum]
  have he : (∑ i, 36864*(totalDrift (input d i) H+(k:ℝ))) =
      36864*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k) := by
    simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ]
  exact h.trans (he.le.trans (mul_le_mul_of_nonneg_left (child_allowance d H) (by norm_num)))

theorem endpoint_budget (d : Data Ω ι k) {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 1/2) (H : ℕ) :
    integral d H (endpoints d ξ) ≤ (160/ξ)*energy d H := by
  have h := sum_le_sum (s:=univ) fun i _ => FineVariation.endpoint_budget (input d i) d.weight
    (fun _ => rfl) hξ hξ' H
  simp only [Fintype.card_fin] at h
  change integral d H (fun t ω => ∑ i, FineVariation.endpointVariation (input d i) ξ t ω) ≤ _
  rw [integral_sum]
  have he : (∑ i, (160/ξ)*(totalDrift (input d i) H+(k:ℝ))) =
      (160/ξ)*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k) := by
    simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ]
  exact h.trans (he.le.trans (mul_le_mul_of_nonneg_left (child_allowance d H) (by positivity)))

theorem size_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω)) ≤
      (10:ℝ)^30*energy d H := by
  have hs := StarBudget.size_budget d H
  have he := child_allowance d H
  have hi := (allowance_bounds ι k).2.2.1.trans (allowance_le_energy d H)
  change integral d H (fun t ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω)) ≤ _ at hs
  norm_num [sizeTolerance,cutoff] at hs
  have hn := energy_nonneg d H
  nlinarith only [hs,he,hi,hn]

theorem parent_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => if parentRefresh d StarConstants.delta t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      (10:ℝ)^30*energy d H := by
  have hs := StarBudget.parent_budget d StarConstants.delta_bounds.1 StarConstants.delta_bounds.2
    (le_refl (1+2/StarConstants.delta)) H
  change integral d H (fun t ω => if parentRefresh d StarConstants.delta t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤ _ at hs
  norm_num [StarConstants.delta] at hs ⊢
  have he := parent_allowance d H
  have hn := energy_nonneg d H
  nlinarith only [hs,he,hn]

theorem wholesale_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (wholesaleMass d) ≤ (10:ℝ)^33*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (wholesale_path d H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (wholesaleMass d) ≤ 203*integral d H _+integral d H _ at h
  have hs := size_budget d H
  have hp := parent_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,hs,hp,hn]

theorem coarse_endpoints (d : Data Ω ι k) (H : ℕ) :
    integral d H (endpoints d sizeTolerance) ≤ 160000*energy d H := by
  have h := endpoint_budget d
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) (show sizeTolerance < 1/2 by norm_num [sizeTolerance]) H
  norm_num [sizeTolerance] at h ⊢
  exact h

theorem deficit_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (StarOutputMovement.deficitMove d) ≤ (10:ℝ)^36*energy d H := by
  have h := integral_mono d H (deficit_step d)
  simp only [integral_add,integral_mul] at h
  have he := coarse_endpoints d H
  have hc := core_budget d H
  have hw := wholesale_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,he,hc,hw,hn]

theorem side_flags_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (SideFiniteInput.changes (StarOutputData.sideData d hk)) ≤ (10:ℝ)^35*energy d H := by
  have h := integral_mono d H (side_changes d hk)
  simp only [integral_add,integral_mul] at h
  have hc := core_budget d H
  have hw := wholesale_budget d H
  have hn := energy_nonneg d H
  nlinarith only [h,hc,hw,hn]

end UniformKServer.StarCoarseBudgets

end


end

end OAI
