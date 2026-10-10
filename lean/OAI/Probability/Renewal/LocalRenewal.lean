import OAI.Probability.Renewal.ScaledWindow
import OAI.Probability.Renewal.Untilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

theorem local_renewal_mass (p : PMF ℕ) (_hp : p 0 = 0) (hspan : SpanOne p)
    {a : ℝ} (ha : 0 < a ∧ a < 1) (hpower : BoundedPowerInput p a) :
    ∃ c > 0, ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (c * (m : ℝ) ^ (a - 1)) ≤ renewalMass p m := by
  obtain ⟨ω, hω, L, hL, εloc, hεloc, N, hlocal⟩ := uniform_tilted_local p hspan ha hpower
  obtain ⟨M⟩ := momentData_exists p ha hpower
  obtain ⟨εZ, hεZ, hZ⟩ := laplace_small p ha.1 hpower
  obtain ⟨c, hc, C, hC, x₀, hx₀, htail, hdef⟩ := hpower
  let A := M.muUpper * (L + 1)
  have hA : 0 < A := mul_pos M.muUpper_pos (by linarith)
  have hAL : L ≤ A / M.muUpper := by
    dsimp [A]
    rw [mul_div_cancel_left₀ _ M.muUpper_pos.ne']
    linarith
  let b := Real.sqrt (M.varLower / (M.muUpper * A))
  let B := Real.sqrt (2 * M.varUpper / (M.muLower * A))
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity [M.varLower_pos, M.muUpper_pos])
  have hB : 0 < B := Real.sqrt_pos.mpr (by positivity [M.varUpper_pos, M.muLower_pos])
  have hω0 : 0 < ω := zero_lt_one.trans_le hω
  let r := min 1 (b / (2 * ω))
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrω : r * ω ≤ b := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * ω)).mp (min_le_right (1 : ℝ) (b / (2 * ω)))
    dsimp [r]
    nlinarith [mul_pos hr hω0]
  let cx := A ^ (1 - a) / M.muUpper
  have hcx : 0 < cx := div_pos (Real.rpow_pos_of_pos hA _) M.muUpper_pos
  let K := 2 * A / M.muLower
  let e := Real.exp (-2 * C * K) * Real.exp (-1) / (8 * Real.pi * B)
  have he : 0 < e := by dsimp [e]; positivity
  let ε := min M.epsilon (min εloc (min εZ x₀⁻¹))
  have hε : 0 < ε := lt_min M.epsilon_pos (lt_min hεloc (lt_min hεZ (inv_pos.mpr hx₀)))
  have hu_lim : Tendsto (fun m : ℕ => A / (m : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat A
  have hx_lim : Tendsto (fun m : ℕ => cx * (m : ℝ) ^ a) atTop atTop :=
    Tendsto.const_mul_atTop hcx ((tendsto_rpow_atTop ha.1).comp tendsto_natCast_atTop_atTop)
  refine ⟨e * r * cx / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hu_lim.eventually (Iio_mem_nhds hε),
    hx_lim.eventually_ge_atTop (N : ℝ), hx_lim.eventually_ge_atTop (2 / r)] with m hm hue hNx hrx
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hmpos
  let u := A / (m : ℝ)
  have hu : 0 < u := div_pos hA hm'
  have hdeps : u ≤ M.epsilon ∧ u ≤ εloc ∧ u ≤ εZ ∧ u ≤ x₀⁻¹ := by
    simpa only [ε, le_min_iff] using hue.le
  let q := tilt p u hu.le
  let μ := natMean q
  let x := (m : ℝ) / μ
  obtain ⟨hx, hxlo, hxuLo, hxuHi⟩ := M.center_bounds hA hm' hdeps.1
  change 0 < x at hx
  change cx * (m : ℝ) ^ a ≤ x at hxlo
  change A / M.muUpper ≤ x * u ^ a at hxuLo
  change x * u ^ a ≤ A / M.muLower at hxuHi
  have hNreal : (N : ℝ) ≤ x := hNx.trans hxlo
  have hrx' : 2 ≤ r * x := by
    have hh := hrx.trans hxlo
    exact (div_le_iff₀ hr).mp hh |>.trans_eq (mul_comm _ _)
  have hcard : r * x / 2 ≤ ((indexWindow x r).card : ℝ) := card_indexWindow hx.le hr.le hrx'
  have hper : ∀ k ∈ indexWindow x r, e / (m : ℝ) ≤ (sumLaw p k m).toReal := by
    intro k hk
    obtain ⟨hklo, hkhi⟩ := mem_indexWindow hx.le hr.le hk
    have hkN : N ≤ k := by exact_mod_cast hNreal.trans hklo
    have hku : L ≤ (k : ℝ) * u ^ a :=
      (hAL.trans hxuLo).trans (mul_le_mul_of_nonneg_right hklo (Real.rpow_pos_of_pos hu a).le)
    have hkuHi : (k : ℝ) * u ^ a ≤ K := by
      have hk2 : (k : ℝ) ≤ 2 * x := hkhi.trans (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right hk2 (Real.rpow_pos_of_pos hu a).le
      calc
        _ ≤ 2 * (x * u ^ a) := by nlinarith [hh]
        _ ≤ 2 * (A / M.muLower) := mul_le_mul_of_nonneg_left hxuHi (by norm_num)
        _ = K := by dsimp [K]; ring
    let σ := Real.sqrt ((k : ℝ) * natVariance q)
    have hsig := M.sigma_window_bounds hA hm' hdeps.1 hr.le hr1 hk
    change b * (m : ℝ) ≤ σ ∧ σ ≤ B * (m : ℝ) at hsig
    have hσ : 0 < σ := (mul_pos hb hm').trans_le hsig.1
    have hcenter : |((m : ℝ) - k * μ) / σ| * ω ≤ 1 :=
      M.centered_window hA hm' hdeps.1 hr.le hr1 hω0.le hrω hk
    have hpr := hlocal u hu hdeps.2.1 k hkN hku m hcenter
    change Real.exp (-1) / (8 * Real.pi * σ) ≤ (sumLaw q k m).toReal at hpr
    have hden : Real.exp (-1) / (8 * Real.pi * (B * (m : ℝ))) ≤
        Real.exp (-1) / (8 * Real.pi * σ) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
      exact mul_le_mul_of_nonneg_left hsig.2 (by positivity)
    have hupr := untilt_lower (m := m) p hu.le (hZ u hu hdeps.2.2.1) hC.le (hdef u hu hdeps.2.2.2).2 hkuHi
    have htot := (mul_le_mul_of_nonneg_left (hden.trans hpr) (Real.exp_pos (-2 * C * K)).le).trans hupr
    calc
      e / (m : ℝ) = Real.exp (-2 * C * K) * (Real.exp (-1) / (8 * Real.pi * (B * (m : ℝ)))) := by
        dsimp [e]
        ring
      _ ≤ _ := htot
  have hfin := renewal_lower_finset p hmpos (indexWindow x r) hper
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hfin
  have hcard' : r * cx * (m : ℝ) ^ a / 2 ≤ ((indexWindow x r).card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hxlo hr.le
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hcard' (div_pos he hm').le
  calc
    _ = (e / (m : ℝ)) * (r * cx * (m : ℝ) ^ a / 2) := by
      rw [Real.rpow_sub hm', Real.rpow_one]
      ring
    _ ≤ _ := hh

end HoneycombLocal

end

end OAI
