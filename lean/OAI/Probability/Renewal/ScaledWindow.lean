import OAI.Probability.Renewal.UniformLocal
import OAI.Probability.Renewal.Counting

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma power_moment_ratio {u : ℝ} (hu : 0 < u) (a c d : ℝ) :
    (c * u ^ (a - 2)) / (d * u ^ (a - 1)) = c / (d * u) := by
  calc
    _ = (c / d) * (u ^ (a - 2) / u ^ (a - 1)) := by ring
    _ = (c / d) * u ^ ((a - 2) - (a - 1)) := by rw [Real.rpow_sub hu (a - 2) (a - 1)]
    _ = _ := by rw [show (a - 2) - (a - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one]; ring

namespace MomentData
variable {p : PMF ℕ} {a : ℝ} (M : MomentData p a)

lemma mean_pos {u : ℝ} (hu : 0 < u) (hue : u ≤ M.epsilon) :
    0 < natMean (tilt p u hu.le) :=
  (mul_pos M.muLower_pos (Real.rpow_pos_of_pos hu _)).trans_le (M.mean_lower u hu hue)

lemma ratio_bounds {u : ℝ} (hu : 0 < u) (hue : u ≤ M.epsilon) :
    M.varLower / (M.muUpper * u) ≤ natVariance (tilt p u hu.le) / natMean (tilt p u hu.le) ∧
    natVariance (tilt p u hu.le) / natMean (tilt p u hu.le) ≤ M.varUpper / (M.muLower * u) := by
  have hμ := M.mean_pos hu hue
  have hv := M.var_lower u hu hue
  have hv0 : 0 ≤ natVariance (tilt p u hu.le) := natVariance_nonneg _
  constructor
  · rw [← power_moment_ratio hu a M.varLower M.muUpper]
    exact div_le_div₀ (by positivity [M.varLower_pos]) hv hμ (M.mean_upper u hu hue)
  · rw [← power_moment_ratio hu a M.varUpper M.muLower]
    exact div_le_div₀ (by positivity [M.varUpper_pos]) (M.var_upper u hu hue) (by positivity [M.muLower_pos]) (M.mean_lower u hu hue)

lemma center_bounds {A m : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hue : A / m ≤ M.epsilon) :
    let u := A / m
    let μ := natMean (tilt p u (div_pos hA hm).le)
    let x := m / μ
    0 < x ∧ (A ^ (1 - a) / M.muUpper) * m ^ a ≤ x ∧
      A / M.muUpper ≤ x * u ^ a ∧ x * u ^ a ≤ A / M.muLower := by
  intro u μ x
  have hu : 0 < u := div_pos hA hm
  have hμ : 0 < μ := M.mean_pos hu hue
  have hl := M.mean_lower u hu hue
  have hh := M.mean_upper u hu hue
  have hLo : m / (M.muUpper * u ^ (a - 1)) ≤ x :=
    div_le_div_of_nonneg_left hm.le hμ hh
  have hHi : x ≤ m / (M.muLower * u ^ (a - 1)) :=
    div_le_div_of_nonneg_left hm.le (by positivity [M.muLower_pos]) hl
  have hid (c : ℝ) : m / (c * u ^ (a - 1)) * u ^ a = A / c := by
    have hpow : u ^ a = u ^ (a - 1) * u := by simpa using Real.rpow_add_one hu.ne' (a - 1)
    rw [hpow]
    dsimp [u]
    field_simp
  refine ⟨div_pos hm hμ, ?_, ?_, ?_⟩
  · have hid' : m / (M.muUpper * u ^ (a - 1)) = (A ^ (1 - a) / M.muUpper) * m ^ a := by
      calc
        _ = (m / (A / m) ^ (a - 1)) / M.muUpper := by dsimp [u]; ring
        _ = _ := by rw [inverse_tilt_scale hA hm]; ring
    rwa [hid'] at hLo
  · have ht := mul_le_mul_of_nonneg_right hLo (Real.rpow_pos_of_pos hu a).le
    rwa [hid] at ht
  · have ht := mul_le_mul_of_nonneg_right hHi (Real.rpow_pos_of_pos hu a).le
    rwa [hid] at ht

lemma sigma_window_bounds {A m r : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hue : A / m ≤ M.epsilon) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {k : ℕ} (hk : k ∈ indexWindow (m / natMean (tilt p (A / m) (div_pos hA hm).le)) r) :
    let σ := Real.sqrt ((k : ℝ) * natVariance (tilt p (A / m) (div_pos hA hm).le))
    Real.sqrt (M.varLower / (M.muUpper * A)) * m ≤ σ ∧
      σ ≤ Real.sqrt (2 * M.varUpper / (M.muLower * A)) * m := by
  intro σ
  let u := A / m
  let μ := natMean (tilt p u (div_pos hA hm).le)
  let v := natVariance (tilt p u (div_pos hA hm).le)
  let x := m / μ
  have hu : 0 < u := div_pos hA hm
  have hμ : 0 < μ := M.mean_pos hu hue
  have hx : 0 < x := div_pos hm hμ
  obtain ⟨hklo, hkhi⟩ := mem_indexWindow hx.le hr hk
  have hk2 : (k : ℝ) ≤ 2 * x := hkhi.trans (by nlinarith)
  have hv : 0 ≤ v := natVariance_nonneg _
  have hkv : 0 ≤ (k : ℝ) * v := mul_nonneg (Nat.cast_nonneg _) hv
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = (k : ℝ) * v := Real.sq_sqrt hkv
  obtain ⟨hrlo, hrhi⟩ := M.ratio_bounds hu hue
  have hlo : M.varLower / (M.muUpper * A) * m ^ 2 ≤ σ ^ 2 := by
    calc
      _ = m * (M.varLower / (M.muUpper * u)) := by dsimp [u]; field_simp
      _ ≤ m * (v / μ) := mul_le_mul_of_nonneg_left hrlo hm.le
      _ = x * v := by dsimp [x]; ring
      _ ≤ (k : ℝ) * v := mul_le_mul_of_nonneg_right hklo hv
      _ = σ ^ 2 := hσ2.symm
  have hhi : σ ^ 2 ≤ (2 * M.varUpper / (M.muLower * A)) * m ^ 2 := by
    calc
      _ = (k : ℝ) * v := hσ2
      _ ≤ 2 * x * v := mul_le_mul_of_nonneg_right hk2 hv
      _ = 2 * m * (v / μ) := by dsimp [x]; ring
      _ ≤ 2 * m * (M.varUpper / (M.muLower * u)) := mul_le_mul_of_nonneg_left hrhi (by positivity)
      _ = _ := by dsimp [u]; field_simp
  have hblo : 0 ≤ M.varLower / (M.muUpper * A) := by positivity [M.varLower_pos, M.muUpper_pos]
  have hbhi : 0 ≤ 2 * M.varUpper / (M.muLower * A) := by positivity [M.varUpper_pos, M.muLower_pos]
  have hsql := Real.sq_sqrt hblo
  have hsqh := Real.sq_sqrt hbhi
  constructor
  · nlinarith [Real.sqrt_nonneg (M.varLower / (M.muUpper * A)), sq_nonneg σ]
  · nlinarith [Real.sqrt_nonneg (2 * M.varUpper / (M.muLower * A)),
      mul_nonneg (Real.sqrt_nonneg (2 * M.varUpper / (M.muLower * A))) hm.le]

lemma centered_window {A m r ω : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hue : A / m ≤ M.epsilon) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hω : 0 ≤ ω)
    (hrω : r * ω ≤ Real.sqrt (M.varLower / (M.muUpper * A)))
    {k : ℕ} (hk : k ∈ indexWindow (m / natMean (tilt p (A / m) (div_pos hA hm).le)) r) :
    let μ := natMean (tilt p (A / m) (div_pos hA hm).le)
    let σ := Real.sqrt ((k : ℝ) * natVariance (tilt p (A / m) (div_pos hA hm).le))
    |(m - k * μ) / σ| * ω ≤ 1 := by
  intro μ σ
  have hμ : 0 < μ := M.mean_pos (div_pos hA hm) hue
  have hx : 0 < m / μ := div_pos hm hμ
  obtain ⟨hklo, hkhi⟩ := mem_indexWindow hx.le hr hk
  have hlo := (M.sigma_window_bounds hA hm hue hr hr1 hk).1
  have hσ : 0 < σ := (mul_pos (Real.sqrt_pos.mpr (by positivity [M.varLower_pos, M.muUpper_pos])) hm).trans_le hlo
  have hkm : m ≤ (k : ℝ) * μ := (div_le_iff₀ hμ).mp hklo
  have hkmax : (k : ℝ) * μ ≤ (1 + r) * m := by
    have hh := mul_le_mul_of_nonneg_right hkhi hμ.le
    field_simp at hh
    exact hh
  rw [abs_div, abs_of_pos hσ, abs_of_nonpos (by linarith : m - (k : ℝ) * μ ≤ 0)]
  have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) * μ - m ≤ r * m by linarith) hω
  have hmul2 := mul_le_mul_of_nonneg_right hrω hm.le
  have hb : (-(m - (k : ℝ) * μ)) * ω ≤ σ := by nlinarith
  calc
    _ = (-(m - (k : ℝ) * μ) * ω) / σ := by ring
    _ ≤ 1 := (div_le_one hσ).mpr hb

end MomentData
end HoneycombLocal

end

end OAI
