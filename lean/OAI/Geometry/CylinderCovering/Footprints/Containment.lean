import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.FootprintContainment

theorem canonical_radial_error {ε x δ D ρ u : ℝ}
    (hε : 0 ≤ ε) (hx : |x| ≤ 2) (hδ : |δ| ≤ D)
    (hu : u = ρ - ε * x * δ) : |u - ρ| ≤ 2 * ε * D := by
  rw [hu, show ρ - ε * x * δ - ρ = -(ε * x * δ) by ring, abs_neg,
    abs_mul, abs_mul, abs_of_nonneg hε]
  have hD : 0 ≤ D := (abs_nonneg δ).trans hδ
  nlinarith only [mul_le_mul (mul_le_mul_of_nonneg_left hx hε) hδ
    (abs_nonneg δ) (by positivity : 0 ≤ ε * 2)]

theorem canonical_transverse_error {ε x δ D : ℝ}
    (hε : 0 ≤ ε) (hx : |x| ≤ 2) (hδ : |δ| ≤ D) :
    |ε * x / 2 * δ ^ 2| ≤ ε * D ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg δ).trans hδ
  have hδ2 : δ ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg δ) hD).2 hδ
  rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hε, abs_of_nonneg (sq_nonneg δ)]
  norm_num
  have hc : ε * |x| / 2 ≤ ε := by nlinarith only [mul_le_mul_of_nonneg_left hx hε]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg δ)).trans
    (mul_le_mul_of_nonneg_left hδ2 hε)

theorem arbitrary_tag_absolute_footprint {ε x q c m d M A B ρ u Y : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d) (hqm : |q - m| ≤ d / 2)
    (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M) (hA : 2 * ε ≤ A) (hB : ε ≤ B)
    (hu : u = ρ - ε * x * (q - c))
    (hY : Y = q * u + ε * x / 2 * (q - c) ^ 2) :
    -A * d ≤ u ∧ u ≤ M + A * d ∧
      |Y - m * u| ≤ d / 2 * |u| + B * d ^ 2 := by
  have hr := canonical_radial_error hε hx hqc hu
  have ht := canonical_transverse_error hε hx hqc
  have hAd := mul_le_mul_of_nonneg_right hA hd
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp hr).1]
  · linarith [(abs_le.mp hr).2]
  · calc
      |Y - m * u| = |(q - m) * u + ε * x / 2 * (q - c) ^ 2| := by rw [hY]; ring_nf
      _ ≤ |(q - m) * u| + |ε * x / 2 * (q - c) ^ 2| := abs_add_le _ _
      _ ≤ d / 2 * |u| + ε * d ^ 2 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hqm (abs_nonneg u)) ht
      _ ≤ d / 2 * |u| + B * d ^ 2 := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hB (sq_nonneg d))

theorem midpoint_absolute_footprint {ε x q c d M A B ρ u Y : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2)
    (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M) (hA : ε ≤ A) (hB : ε / 4 ≤ B)
    (hu : u = ρ - ε * x * (q - c))
    (hY : Y = q * u + ε * x / 2 * (q - c) ^ 2) :
    -A * d ≤ u ∧ u ≤ M + A * d ∧
      |Y - c * u| ≤ d / 2 * |u| + B * d ^ 2 := by
  have hr := canonical_radial_error hε hx hqc hu
  have ht := canonical_transverse_error hε hx hqc
  have hAd := mul_le_mul_of_nonneg_right hA hd
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp hr).1]
  · linarith [(abs_le.mp hr).2]
  · calc
      |Y - c * u| = |(q - c) * u + ε * x / 2 * (q - c) ^ 2| := by rw [hY]; ring_nf
      _ ≤ |(q - c) * u| + |ε * x / 2 * (q - c) ^ 2| := abs_add_le _ _
      _ ≤ d / 2 * |u| + ε * (d / 2) ^ 2 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hqc (abs_nonneg u)) ht
      _ ≤ d / 2 * |u| + B * d ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hB (sq_nonneg d)]

theorem midpoint_affine_footprint {ε x q c d M A B ρ u Y : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q - c| ≤ d / 2)
    (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M) (hA : ε ≤ A) (hB : 3 * ε / 4 ≤ B)
    (hu : u = ρ - ε * x * (q - c))
    (hY : Y = q * u + ε * x / 2 * (q - c) ^ 2) :
    -A * d ≤ u ∧ u ≤ M + A * d ∧
      |Y - c * u| ≤ d / 2 * u + B * d ^ 2 := by
  have hr := canonical_radial_error hε hx hqc hu
  have ht := canonical_transverse_error hε hx hqc
  have hAd := mul_le_mul_of_nonneg_right hA hd
  have hρu : ρ ≤ u + ε * d := by linarith [(abs_le.mp hr).1]
  have hwidth : |Y - c * u| ≤ d / 2 * ρ + ε * (d / 2) ^ 2 := by
    calc
      |Y - c * u| = |(q - c) * ρ - ε * x / 2 * (q - c) ^ 2| := by
        rw [hY, hu]; congr 1; ring
      _ ≤ |(q - c) * ρ| + |ε * x / 2 * (q - c) ^ 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((q - c) * ρ) (-(ε * x / 2 * (q - c) ^ 2))
      _ ≤ d / 2 * ρ + ε * (d / 2) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hρ0]
        exact add_le_add (mul_le_mul_of_nonneg_right hqc hρ0) ht
  refine ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2], ?_⟩
  have hscale := mul_le_mul_of_nonneg_left hρu (by positivity : 0 ≤ d / 2)
  have hBscale := mul_le_mul_of_nonneg_right hB (sq_nonneg d)
  nlinarith only [hwidth, hscale, hBscale]

theorem endpoint_affine_footprint {ε x q c d M ρ u Y : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc0 : 0 ≤ q - c) (hqcd : q - c ≤ d)
    (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hu : u = ρ - ε * x * (q - c))
    (hY : Y = q * u + ε * x / 2 * (q - c) ^ 2) :
    -2 * ε * d ≤ u ∧ u ≤ M + 2 * ε * d ∧
      -3 * ε * d ^ 2 ≤ Y - c * u ∧
      Y - c * u ≤ d * u + 3 * ε * d ^ 2 := by
  have hqc : |q - c| ≤ d := by rwa [abs_of_nonneg hqc0]
  have hr := canonical_radial_error hε hx hqc hu
  have ht := canonical_transverse_error hε hx hqc
  have hul : -2 * ε * d ≤ u := by linarith [(abs_le.mp hr).1]
  have huu : u ≤ M + 2 * ε * d := by linarith [(abs_le.mp hr).2]
  have hprod : -2 * ε * d ^ 2 ≤ (q - c) * u ∧
      (q - c) * u ≤ d * u + 2 * ε * d ^ 2 := by
    by_cases hu0 : 0 ≤ u
    · constructor
      · have hp := mul_nonneg hqc0 hu0
        have he := mul_nonneg hε (sq_nonneg d)
        nlinarith only [hp, he]
      · have hp := mul_le_mul_of_nonneg_right hqcd hu0
        have he := mul_nonneg hε (sq_nonneg d)
        nlinarith only [hp, he]
    · have hun : u ≤ 0 := le_of_not_ge hu0
      have hp0 := mul_nonpos_of_nonneg_of_nonpos hqc0 hun
      have hpd := mul_le_mul_of_nonpos_right hqcd hun
      have hlower := mul_le_mul_of_nonneg_left hul hd
      constructor <;> nlinarith only [hp0, hpd, hlower]
  have hid : Y - c * u = (q - c) * u + ε * x / 2 * (q - c) ^ 2 := by
    rw [hY]; ring
  refine ⟨hul, huu, ?_, ?_⟩ <;> rw [hid] <;>
    linarith [(abs_le.mp ht).1, (abs_le.mp ht).2, hprod.1, hprod.2]

theorem unit_edge_triangle {η x s m d M ρ c b : ℝ}
    (hη : 0 ≤ η) (hd : 0 ≤ d) (hx : |x| ≤ 1 / 2)
    (hsm : |s - m| ≤ d / 2) (hρ0 : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hc : c = ρ + 2 * η * x * (s - m))
    (hb : b - m * c = (s - m) * ρ + η * x * (s - m) ^ 2) :
    -η * d ≤ c ∧ c ≤ M + η * d ∧
      |b - m * c| ≤ d / 2 * (c + η * d) := by
  have hx' : |(-4) * x| ≤ 2 := by
    rw [abs_mul]
    norm_num
    linarith
  have hc' : c = ρ - (η / 2) * ((-4) * x) * (s - m) := by rw [hc]; ring
  have hr := canonical_radial_error (by positivity : 0 ≤ η / 2) hx' hsm hc'
  have hx'' : |2 * x| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have ht := canonical_transverse_error hη hx'' hsm
  have ht' : |η * x * (s - m) ^ 2| ≤ η * (d / 2) ^ 2 := by
    convert ht using 1
    congr 1
    ring
  have hρc : ρ ≤ c + η * d / 2 := by linarith [(abs_le.mp hr).1]
  have hwidth : |b - m * c| ≤ d / 2 * ρ + η * (d / 2) ^ 2 := by
    rw [hb]
    calc
      _ ≤ |(s - m) * ρ| + |η * x * (s - m) ^ 2| := abs_add_le _ _
      _ ≤ d / 2 * ρ + η * (d / 2) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hρ0]
        exact add_le_add (mul_le_mul_of_nonneg_right hsm hρ0) ht'
  have he := mul_nonneg hη hd
  refine ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2], ?_⟩
  have hscale := mul_le_mul_of_nonneg_left hρc (by positivity : 0 ≤ d / 2)
  nlinarith only [hwidth, hscale]

theorem halfheight_trapezoid {r p ρ e M u σ v w : ℝ}
    (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hr : |r - p| ≤ ρ)
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hσ : |σ| ≤ e)
    (hv : v = u * r + σ * (r + p) / 2) (hw : w = u + σ) :
    -e ≤ w ∧ w ≤ M + e ∧ |v - p * w| ≤ ρ * (w + 2 * e) := by
  have hσl := (abs_le.mp hσ).1
  have hσr := (abs_le.mp hσ).2
  have huv : |u + σ / 2| ≤ u + e / 2 := by
    calc
      |u + σ / 2| ≤ |u| + |σ / 2| := abs_add_le _ _
      _ = u + |σ| / 2 := by rw [abs_of_nonneg hu0, abs_div]; norm_num
      _ ≤ u + e / 2 := by linarith
  refine ⟨by rw [hw]; linarith, by rw [hw]; linarith, ?_⟩
  calc
    |v - p * w| = |r - p| * |u + σ / 2| := by
      rw [← abs_mul, hv, hw]; congr 1; ring
    _ ≤ ρ * (u + e / 2) := mul_le_mul hr huv (abs_nonneg _) hρ
    _ ≤ ρ * (w + 2 * e) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      rw [hw]
      linarith

theorem halfheight_displacement {δ X r p ρ : ℝ}
    (hδ : 0 ≤ δ) (hX : |X| ≤ 1) (hr : |r - p| ≤ ρ) :
    |δ * X * (r - p) / 2| ≤ δ * ρ / 2 := by
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hδ]
  norm_num
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hr
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hX hδ) hr
    (abs_nonneg _) (by positivity : 0 ≤ δ * 1)
  nlinarith only [h]

theorem absolute_footprint_not_convex {A B d M m : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hd : 0 < d) (hM : 0 ≤ M) :
    ¬ Convex ℝ {z : ℝ × ℝ | -A * d ≤ z.1 ∧ z.1 ≤ M + A * d ∧
      |z.2 - m * z.1| ≤ d / 2 * |z.1| + B * d ^ 2} := by
  let w : ℝ := d / 2 * (A * d) + B * d ^ 2
  have hAd : 0 < A * d := mul_pos hA hd
  have hw : 0 ≤ w := by dsimp [w]; positivity
  let a : ℝ × ℝ := (-A * d, m * (-A * d) + w)
  let b : ℝ × ℝ := (A * d, m * (A * d) + w)
  have ha : a ∈ {z : ℝ × ℝ | -A * d ≤ z.1 ∧ z.1 ≤ M + A * d ∧
      |z.2 - m * z.1| ≤ d / 2 * |z.1| + B * d ^ 2} := by
    change -A * d ≤ -A * d ∧ -A * d ≤ M + A * d ∧
      |m * (-A * d) + w - m * (-A * d)| ≤ d / 2 * |-A * d| + B * d ^ 2
    refine ⟨le_rfl, by linarith, ?_⟩
    rw [add_sub_cancel_left, abs_of_nonneg hw]
    have habs : |-A * d| = A * d := by rw [abs_of_neg (by nlinarith)]; ring
    rw [habs]
  have hb : b ∈ {z : ℝ × ℝ | -A * d ≤ z.1 ∧ z.1 ≤ M + A * d ∧
      |z.2 - m * z.1| ≤ d / 2 * |z.1| + B * d ^ 2} := by
    change -A * d ≤ A * d ∧ A * d ≤ M + A * d ∧
      |m * (A * d) + w - m * (A * d)| ≤ d / 2 * |A * d| + B * d ^ 2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [add_sub_cancel_left, abs_of_nonneg hw, abs_of_pos hAd]
  intro hconv
  have hmid := hconv ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have heq : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (0, w) := by
    ext <;> dsimp [a, b] <;> ring
  rw [heq] at hmid
  have hbad : w ≤ B * d ^ 2 := by simpa [abs_of_nonneg hw] using hmid.2.2
  dsimp [w] at hbad
  have hp := mul_pos hd hAd
  nlinarith only [hbad, hp]

end CylinderCovering.FootprintContainment

end

end OAI
