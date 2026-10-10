import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Extending finite-scale sphere cap estimates to arbitrary ball centers -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

 theorem sphere_cap_arbitrary_center (ν : Measure (Sphere d))
    {R L s : ℝ} (hR : 1 ≤ R) (hL : 1 ≤ L) (hs : 0 ≤ s) (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν (ball w r) ≤ ENNReal.ofReal (L*r^s))
    (x : Space d) {r : ℝ} (hr : R⁻¹ ≤ r) (_hr1 : r ≤ 1) :
    ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal ((2:ℝ)^s*L*r^s) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hrp : 0 < r := (inv_pos.mpr hRp).trans_le hr
  have he : L*(2*r)^s = (2:ℝ)^s*L*r^s := by
    rw [Real.mul_rpow (by norm_num) hrp.le]
    ring
  by_cases hsmall : 2*r ≤ 1
  · by_cases hne : {w : Sphere d | dist (w:Space d) x < r}.Nonempty
    · obtain ⟨w,hw⟩ := hne
      have hsub : {u : Sphere d | dist (u:Space d) x < r} ⊆ ball w (2*r) := by
        intro u hu
        apply lt_of_le_of_lt (dist_triangle (u:Space d) x (w:Space d))
        change dist (u:Space d) x+dist x (w:Space d) < 2*r
        rw [dist_comm x]
        change dist (w:Space d) x < r at hw
        change dist (u:Space d) x < r at hu
        linarith
      exact (measure_mono hsub).trans ((hball w (2*r) (by linarith) hsmall).trans_eq (by rw [he]))
    · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
      exact zero_le
  · have hpower : 1 ≤ L*(2*r)^s :=
      one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow (by linarith) hs)
    exact (measure_mono (subset_univ _)).trans (hmass.trans (by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rwa [he] at hpower))

end Falconer

end OAI
