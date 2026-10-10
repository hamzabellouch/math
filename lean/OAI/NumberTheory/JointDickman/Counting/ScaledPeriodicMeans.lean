import OAI.NumberTheory.JointDickman.Counting.RealPeriodicMoments
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteResidues
import OAI.NumberTheory.JointDickman.Amplification.AmplificationVolumeProducts

namespace OAI

/-! # Periodic means on the multiplier interval -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem quotient_endpoint_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N/d+1 : ℕ) : ℝ)/(N : ℝ)) atTop (nhds (1/(d : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ 1/(d : ℝ) by positivity)).comp
    tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (nhds (1/(d : ℝ))) := by
    simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast] using h
  have hh := he.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hh

theorem mean_scaled_prefix {f : ℕ → ℝ} {μ : ℝ}
    (h : Tendsto (fun N => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (nhds μ))
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (∑ n ∈ range (N/d+1), f n)/(N : ℝ)) atTop (nhds (μ/(d : ℝ))) := by
  have he : Tendsto (fun N : ℕ => N/d+1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right (N/d) 1)
      (Nat.tendsto_div_const_atTop (ne_of_gt hd))
  have hm := (h.comp he).mul (quotient_endpoint_ratio hd)
  have hid (N : ℕ) : ((∑ n ∈ range (N/d+1), f n)/((N/d+1 : ℕ) : ℝ)) *
      (((N/d+1 : ℕ) : ℝ)/(N : ℝ)) = (∑ n ∈ range (N/d+1), f n)/(N : ℝ) := by
    have hn : ((N/d+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [Function.comp_def, hid, mul_one_div] using hm

theorem baseArithmeticResidueWeight_natCast (B n : ℕ) :
    baseArithmeticResidueWeight B (n : ZMod (auxiliarySquarePeriod B)).val =
      baseArithmeticResidueWeight B n := by
  unfold baseArithmeticResidueWeight
  have hp (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : p ∣ auxiliarySquarePeriod B := by
    simpa only [prod_singleton] using
      (auxiliaryProduct_dvd_period (singleton_subset_iff.mpr hp))
  rw [ZMod.val_natCast]
  congr 1
  exact primeSite_modEq hp (Nat.mod_modEq n (auxiliarySquarePeriod B))

theorem baseArithmeticResidueWeight_mean_tendsto (B : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, baseArithmeticResidueWeight B n)/(N : ℝ))
      atTop (nhds (baseArithmeticResidueMean B)) := by
  have h := real_periodic_moment_tendsto
    (fun a : ZMod (auxiliarySquarePeriod B) => baseArithmeticResidueWeight B a.val) 1
  simpa only [pow_one, baseArithmeticResidueWeight_natCast, baseArithmeticResidueWeight_mean] using h

end JointDickman

end OAI
