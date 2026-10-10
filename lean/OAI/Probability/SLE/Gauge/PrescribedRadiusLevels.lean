import OAI.Probability.SLE.Gauge.BatchRadiusGaps
import OAI.Probability.SLE.Gauge.GaugeEntrySmallness

namespace OAI

/-! Physical logarithmic levels for the exact prescribed radii. Uniformity
  includes moving centers down to height exp(-n). -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

def entryPhysicalLevel (κ : ℝ) (W : WienerLaw) (e : Entry) (A : ℝ) (z : ℂ) : ℝ :=
  Real.log ((2*z.im)/A) + (e.1:ℝ)^2 +
    2*a κ*(entryPosition κ W e:ℝ)*((batchLevel κ W e.1:ℝ)+(e.1:ℝ))

lemma entryPhysicalLevel_radius (κ : ℝ) (W : WienerLaw) (e : Entry)
    {A : ℝ} (hA : 0<A) {z : ℂ} (hz : 0<z.im) :
    (2*z.im)*Real.exp (-entryPhysicalLevel κ W e A z)=A*entryRadius κ W e := by
  have hp : 0<(2*z.im)/A := by positivity
  unfold entryPhysicalLevel entryRadius
  rw [show -(Real.log ((2*z.im)/A)+(e.1:ℝ)^2+
    2*a κ*(entryPosition κ W e:ℝ)*((batchLevel κ W e.1:ℝ)+(e.1:ℝ))) =
    -Real.log ((2*z.im)/A)+(-(e.1:ℝ)^2-
      2*a κ*(entryPosition κ W e:ℝ)*((batchLevel κ W e.1:ℝ)+(e.1:ℝ))) by ring,
    Real.exp_add,Real.exp_neg,Real.exp_log hp]
  field_simp

lemma entryPhysicalLevel_gap {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n : ℕ} (hn : 1≤n) {o o' : Option (ℤ×ℕ)}
    (hpos : entryPosition κ W (n,o)<entryPosition κ W (n,o')) (A : ℝ) (z : ℂ) :
    entryPhysicalLevel κ W (n,o) A z+2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ)) ≤
      entryPhysicalLevel κ W (n,o') A z := by
  have hpN : entryPosition κ W (n,o)+1 ≤ entryPosition κ W (n,o') := hpos
  have hp : (entryPosition κ W (n,o):ℝ)+1 ≤ entryPosition κ W (n,o') := by exact_mod_cast hpN
  have hcoef : 0 ≤ 2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ)) := by
    have ha := internal_a_pos hκ
    positivity
  have hh := mul_le_mul_of_nonneg_left hp hcoef
  dsimp only [entryPhysicalLevel]
  have hnR : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  nlinarith

lemma entryPhysicalLevel_cleanup_gap {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n : ℕ} (hn : 1≤n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) {k : ℤ} {j : ℕ}
    (hj : j < multiplicity κ W n k) (A : ℝ) (z : ℂ) :
    entryPhysicalLevel κ W (n,some (k,j)) A z +
      2*a κ*(batchLevel κ W n:ℝ)+2*a κ*(n:ℝ) ≤
        entryPhysicalLevel κ W (n,none) A z := by
  have hh := entryPhysicalLevel_gap hκ W hn (entryPosition_lt_cleanup κ W hn hm1 hJ hj) A z
  linarith

lemma eventually_entryPhysicalLevel_large {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {A : ℝ} (hA : 0<A) (L : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (o : Option (ℤ×ℕ)) (z : ℂ),
      Real.exp (-(n:ℝ)) ≤ z.im → L<entryPhysicalLevel κ W (n,o) A z := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 2 (L-Real.log (2/A)))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro o z hz
  have hnR : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (2:ℝ)<n := (lt_of_le_of_lt (le_max_left _ _) hN).trans_le hnR
  have hnL : L-Real.log (2/A)<(n:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans_le hnR
  have hlog : Real.log (2/A)-(n:ℝ) ≤ Real.log ((2*z.im)/A) := by
    have hp : 0<2/A := by positivity
    have hh := Real.log_le_log (mul_pos hp (Real.exp_pos (-(n:ℝ))))
      (mul_le_mul_of_nonneg_left hz hp.le)
    rw [Real.log_mul hp.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
    simpa only [sub_eq_add_neg,div_mul_eq_mul_div] using hh
  have hterm : 0 ≤ 2*a κ*(entryPosition κ W (n,o):ℝ)*
      ((batchLevel κ W n:ℝ)+(n:ℝ)) := by
    have ha := internal_a_pos hκ
    positivity
  dsimp only [entryPhysicalLevel]
  nlinarith

end SLEExactGauge.Target

end

end OAI
