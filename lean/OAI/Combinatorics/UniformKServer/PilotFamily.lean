import Mathlib
import OAI.Combinatorics.UniformKServer.DyadicTiers
import OAI.Combinatorics.UniformKServer.PilotTemplates
import OAI.Combinatorics.UniformKServer.FlowAuxiliary

namespace OAI

noncomputable section

/-! Uniform finite pilot family constants: the tier weights sum independently
of the number of tiers and of k. -/
namespace UniformKServer.PilotFamily
open Finset PilotEdits

abbrev Index (k : ℕ) := Option (Fin (DyadicTiers.last (Real.log k)+1))

def template (P : TierPilot.Parameters) {k : ℕ} : Index k→Template
  | none => heavyTemplate
  | some _ => shortTemplate P

def weight {k : ℕ} : Index k→ℝ
  | none => 1
  | some i => Real.exp (-DyadicTiers.value i.val)

theorem weight_nonneg {k : ℕ} (i : Index k) : 0≤weight i := by
  cases i <;> simp only [weight] <;> positivity

theorem weight_sum (k : ℕ) : (∑ i : Index k, weight i)≤3 := by
  rw [Fintype.sum_option]
  change 1+(∑ i : Fin (DyadicTiers.last (Real.log k)+1), Real.exp (-DyadicTiers.value i.val))≤3
  rw [Fin.sum_univ_eq_sum_range (fun i => Real.exp (-DyadicTiers.value i))]
  linarith [DyadicTiers.exponential_sum (DyadicTiers.last (Real.log k)+1)]

def rateBound (P : TierPilot.Parameters) : ℝ := rate heavyTemplate+2*rate (shortTemplate P)

theorem rate_bound (P : TierPilot.Parameters) (k : ℕ) :
    (∑ i : Index k, weight i*rate (template P i))≤rateBound P := by
  rw [Fintype.sum_option]
  simp only [weight,template,one_mul]
  rw [←sum_mul,Fin.sum_univ_eq_sum_range (fun i => Real.exp (-DyadicTiers.value i))]
  have h := mul_le_mul_of_nonneg_right (DyadicTiers.exponential_sum (DyadicTiers.last (Real.log k)+1))
    (rate_nonneg (shortTemplate P))
  dsimp only [rateBound]
  linarith

theorem rateBound_nonneg (P : TierPilot.Parameters) : 0≤rateBound P := by
  exact add_nonneg (rate_nonneg _) (mul_nonneg (by norm_num) (rate_nonneg _))

end UniformKServer.PilotFamily

end

end OAI
