import OAI.NumberTheory.JointDickman.Amplification.ForwardDifference

namespace OAI

/-! # Derivatives of the logarithmic phases in character sums -/
namespace JointDickman
open Set Filter Problem337
open scoped Topology ContDiff

lemma logarithmic_phase_smooth (Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Z*Real.log y) (Ioi 0) :=
  contDiffOn_const.mul (Real.contDiffOn_log.mono (fun _ hx => ne_of_gt hx))

lemma logarithmic_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+1) (fun y : ℝ => Z*Real.log y) x =
      (-1:ℝ)^k*(k.factorial:ℝ)*Z/x^(k+1) := by
  have he : deriv (fun y : ℝ => Z*Real.log y) =ᶠ[𝓝 x] (fun y => Z/y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hd := (Real.hasDerivAt_log (ne_of_gt hy)).const_mul Z
    simpa only [div_eq_mul_inv] using hd.deriv
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq k]
  exact reciprocal_phase_iteratedDeriv k Z x

lemma abs_logarithmic_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv (k+1) (fun y : ℝ => Z*Real.log y) x| =
      (k.factorial:ℝ)*|Z|/x^(k+1) := by
  rw [logarithmic_phase_iteratedDeriv k Z hx]
  simp [abs_div,abs_mul,abs_pow,abs_of_pos hx]

/-- After finitely many positive differences, the second derivative retains
its explicit size throughout the original interval and all shifts. -/
theorem logarithmic_forwardDifference_second_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x+hs.sum ≤ V) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/V^(hs.length+2) ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => Z*Real.log y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => Z*Real.log y)) x| ≤
      hs.prod*((hs.length+1).factorial:ℝ)*|Z|/U^(hs.length+2) := by
  obtain ⟨ξ,hxξ,hξ,he⟩ := iteratedDeriv_forwardDifference_eq 2 hs hhs
    (logarithmic_phase_smooth Z) (hU.trans_le hx)
  have hξ0 : 0 < ξ := hU.trans_le (hx.trans hxξ)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [he,abs_mul,abs_of_nonneg hp]
  rw [show hs.length+2 = (hs.length+1)+1 by omega,
    abs_logarithmic_phase_iteratedDeriv (hs.length+1) Z hξ0]
  constructor
  · have hpow := pow_le_pow_left₀ hξ0.le (hξ.trans hxV) (hs.length+1+1)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hξ0 _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  · have hpow := pow_le_pow_left₀ hU.le (hx.trans hxξ) (hs.length+1+1)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hU _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp

lemma logarithmic_linear_phase_smooth (a Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => a*y+Z*Real.log y) (Ioi 0) :=
  (contDiffOn_const.mul contDiffOn_id).add (logarithmic_phase_smooth Z)

lemma logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x =
      (-1:ℝ)^(k+1)*((k+1).factorial:ℝ)*Z/x^(k+2) := by
  have hlin : ContDiffAt ℝ (k+2) (fun y : ℝ => a*y) x :=
    (contDiff_const.mul contDiff_id).contDiffAt
  have hlog : ContDiffAt ℝ (k+2) (fun y : ℝ => Z*Real.log y) x :=
    ((logarithmic_phase_smooth Z).contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by simp)
  rw [iteratedDeriv_fun_add hlin hlog,iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_fun_id,show k+2 ≠ 0 by omega,show k+2 ≠ 1 by omega,
    ite_false,mul_zero,zero_add]
  exact logarithmic_phase_iteratedDeriv (k+1) Z hx

lemma abs_logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x| =
      ((k+1).factorial:ℝ)*|Z|/x^(k+2) := by
  rw [logarithmic_linear_phase_iteratedDeriv k a Z hx]
  simp [abs_div,abs_mul,abs_pow,abs_of_pos hx]

lemma logarithmic_linear_forwardDifference_second_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x+hs.sum ≤ V) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/V^(hs.length+2) ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ≤
      hs.prod*((hs.length+1).factorial:ℝ)*|Z|/U^(hs.length+2) := by
  obtain ⟨ξ,hxξ,hξ,he⟩ := iteratedDeriv_forwardDifference_eq 2 hs hhs
    (logarithmic_linear_phase_smooth a Z) (hU.trans_le hx)
  have hξ0 : 0 < ξ := hU.trans_le (hx.trans hxξ)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [he,abs_mul,abs_of_nonneg hp,
    abs_logarithmic_linear_phase_iteratedDeriv hs.length a Z hξ0]
  constructor
  · have hpow := pow_le_pow_left₀ hξ0.le (hξ.trans hxV) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hξ0 _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  · have hpow := pow_le_pow_left₀ hU.le (hx.trans hxξ) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hU _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp

end JointDickman

end OAI
