import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums

namespace OAI

/-! # Reciprocal-prime masses on logarithmic intervals -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_power_interval_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨M,hM⟩ := primeReciprocalSum_remainder_tendsto primeReciprocalMertensInput
  have hlim := ((hM.comp (tendsto_rpow_atTop hb)).sub
    (hM.comp (tendsto_rpow_atTop ha))).add_const (Real.log b-Real.log a)
  have heq : (fun x : ℝ =>
      (primeReciprocalSum (x^b)-Real.log (Real.log (x^b))) -
      (primeReciprocalSum (x^a)-Real.log (Real.log (x^a))) +
        (Real.log b-Real.log a)) =ᶠ[atTop]
      (fun x : ℝ => ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hx0.le a)
      (Real.rpow_le_rpow_of_exponent_le hx.le hab),
      Real.log_rpow hx0,Real.log_rpow hx0,
      Real.log_mul hb.ne' hlog.ne',Real.log_mul ha.ne' hlog.ne']
    ring
  simpa only [sub_self,zero_add] using hlim.congr' heq

end JointDickman

end OAI
