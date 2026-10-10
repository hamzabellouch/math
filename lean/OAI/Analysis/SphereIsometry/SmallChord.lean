import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

namespace OAI

/-!
# The small-chord contradiction

The scalar estimates imply nonnegative coefficients in two exact identities
between the actual chord vectors. Applying the norm triangle inequality to
those identities contradicts preservation of the distance between the base
point and the opposite endpoint. No convexity or monotonicity property of an
abstract auxiliary function is assumed.
-/

namespace Tingley

/-- The two small-regime estimates and the strict chord imbalance force the
radial deficit to be strictly below one half. -/
theorem smallChord_epsilon_lt_half {A B d ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1) (hd : d ≤ 2)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 := by
  have step (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hsum : a + b < 1)
      (he : ε ≤ d * a * (1 - b)) : ε < 1 / 2 := by
    have hahalf : a < 1 / 2 := by linarith
    have hb1 : b < 1 := by linarith
    have hprod0 : 0 ≤ a * (1 - b) :=
      mul_nonneg ha.le (sub_nonneg.mpr hb1.le)
    have hprod : a * (1 - b) ≤ a * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) ha.le
    have hsquare : 0 < (1 / 2 - a) ^ 2 :=
      sq_pos_of_pos (by linarith)
    have hquarter : a * (1 - b) < 1 / 4 := by nlinarith
    have hscale : d * (a * (1 - b)) ≤ 2 * (a * (1 - b)) :=
      mul_le_mul_of_nonneg_right hd hprod0
    nlinarith [he, hscale, hquarter]
  rcases le_total A B with h | h
  · exact step A B hA h hAB heA
  · exact step B A hB h (by linarith) heB

/-- The scalar conclusions needed by the two actual vector identities.
The second coefficient is permitted to vanish. -/
theorem smallChord_coefficients {A B d ε t p r s u : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1)
    (hd : 0 < d) (hd2 : d ≤ 2) (hεt : ε + t = 1)
    (hdr : d = p + r) (hds : d = s + u)
    (hpA : p = d * A) (huB : u = d * B)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 ∧ 0 < r * t - p * ε ∧ 0 ≤ s * ε - u * t ∧ p < s := by
  have hehalf := smallChord_epsilon_lt_half hA hB hAB hd2 heA heB
  have hAt : A < t := by linarith
  have hr : r = d - p := by linarith
  have hs : s = d - u := by linarith
  have he : ε = 1 - t := by linarith
  have ht : t = 1 - ε := by linarith
  have hα : r * t - p * ε = d * (t - A) := by
    rw [hr, hpA, he]
    ring
  have hβ : s * ε - u * t = d * (ε - B) := by
    rw [hs, huB, ht]
    ring
  have hgap : s - p = d * (1 - A - B) := by
    rw [hs, hpA, huB]
    ring
  refine ⟨hehalf, ?_, ?_, ?_⟩
  · rw [hα]
    exact mul_pos hd (sub_pos.mpr hAt)
  · rw [hβ]
    exact mul_nonneg hd.le (sub_nonneg.mpr hBe)
  · have hgap_pos : 0 < s - p := by
      rw [hgap]
      exact mul_pos hd (by linarith)
    linarith

/-- Two norm triangle inequalities on the actual chord vectors are incompatible
with the chord imbalance and the preserved base-to-endpoint distance. -/
theorem smallChord_norm_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d : ℝ}
    (hεt : ε + t = 1) (hε : 0 < ε) (hd : 0 < d)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hps : p < s)
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hα : 0 ≤ r * t - p * ε) (hβ : 0 ≤ s * ε - u * t)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  let V : X := ε • y + r • v
  let W : Y := ε • b + u • w
  have hVW : ‖V‖ = ‖W‖ := hiso
  have hleftId : r • (t • y + p • v) = p • V + (r * t - p * ε) • y := by
    dsimp only [V]
    module
  have hrightId : s • W = u • (t • b + s • w) + (s * ε - u * t) • b := by
    dsimp only [W]
    module
  have hleft : r ≤ p * ‖V‖ + (r * t - p * ε) := by
    calc
      r = ‖r • (t • y + p • v)‖ := by
        rw [norm_smul_of_nonneg hr.le, hx, mul_one]
      _ = ‖p • V + (r * t - p * ε) • y‖ := congrArg norm hleftId
      _ ≤ ‖p • V‖ + ‖(r * t - p * ε) • y‖ := norm_add_le _ _
      _ = p * ‖V‖ + (r * t - p * ε) := by
        rw [norm_smul_of_nonneg hp.le, norm_smul_of_nonneg hα, hy, mul_one]
  have hright : s * ‖W‖ ≤ u + (s * ε - u * t) := by
    calc
      s * ‖W‖ = ‖s • W‖ := (norm_smul_of_nonneg hs.le W).symm
      _ = ‖u • (t • b + s • w) + (s * ε - u * t) • b‖ := congrArg norm hrightId
      _ ≤ ‖u • (t • b + s • w)‖ + ‖(s * ε - u * t) • b‖ := norm_add_le _ _
      _ = u + (s * ε - u * t) := by
        simp only [norm_smul_of_nonneg hu.le, norm_smul_of_nonneg hβ, hfx, hb, mul_one]
  have ht : t = 1 - ε := by linarith
  have hrearrange : r - (r * t - p * ε) = ε * d := by
    rw [ht, hdr]
    ring
  have hurearrange : u + (s * ε - u * t) = ε * d := by
    rw [ht, hds]
    ring
  have hlower : ε * d ≤ p * ‖V‖ := by linarith
  have hupper : s * ‖V‖ ≤ ε * d := by rw [hVW]; linarith
  have hpositive : 0 < ε * d := mul_pos hε hd
  have hVpos : 0 < ‖V‖ := by
    by_contra h
    have hVnonpos : ‖V‖ ≤ 0 := le_of_not_gt h
    have hpV : p * ‖V‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hVnonpos
    linarith
  exact (not_lt_of_ge (hupper.trans hlower)) (mul_lt_mul_of_pos_right hps hVpos)

/-- The small regime contradicts preservation of the actual opposite-endpoint
distance. All scalar guards of the norm argument are derived here. -/
theorem smallChord_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d A B : ℝ}
    (ht1 : t < 1) (he : ε = 1 - t)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hd2 : d ≤ 2)
    (hA : A = p / d) (hB : B = u / d) (hAB : A + B < 1)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A))
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  have hd : 0 < d := by rw [hdr]; exact add_pos hp hr
  have hApos : 0 < A := by rw [hA]; exact div_pos hp hd
  have hBpos : 0 < B := by rw [hB]; exact div_pos hu hd
  have hpA : p = d * A := by rw [hA, mul_div_cancel₀ p (ne_of_gt hd)]
  have huB : u = d * B := by rw [hB, mul_div_cancel₀ u (ne_of_gt hd)]
  have hεt : ε + t = 1 := by linarith
  have hε : 0 < ε := by linarith
  obtain ⟨_, hα, hβ, hps⟩ := smallChord_coefficients hApos hBpos hAB hd hd2 hεt
    hdr hds hpA huB hAe hBe heA heB
  exact smallChord_norm_contradiction y v b w hεt hε hd hp hr hs hu hdr hds hps
    hy hb hx hfx hα.le hβ hiso

end Tingley

end OAI
