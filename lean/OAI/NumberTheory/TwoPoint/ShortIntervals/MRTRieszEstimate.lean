import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszBoundary
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszContour
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszTails
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseAbscissa

namespace OAI

/-! The sparse-prime Riesz kernel estimate, with no upper restriction on
the prime cutoff. Far tails are charged to the pole term. -/

namespace TwoPointCorrelations

open Complex Filter Set _root_.Erdos970 _root_.OAI.Erdos970
open scoped Topology

lemma mrt_riesz_finite_shift_simple {x a b T u B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b) (hb2 : b ≤ 2)
    (hu : |u| < T) (hB : 0 ≤ B)
    (hz : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0)
    (hl : ∀ t ∈ Icc (-T) T,
      ‖-deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B)
    (hs : ∀ σ ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
        4 * x / (1 + u ^ 2) + 2 * B * x ^ a + 4 * B * x ^ b / T ^ 3 := by
  have hh := mrt_zeta_riesz_finite_shift hx ha ha1 hb hu hB hz hl hs
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  have hD : 0 ≤ 4 * B * x ^ b / T ^ 3 := by positivity
  have hside : (4 * B * x ^ b / T ^ 3 * (b - a)) / (2 * Real.pi) ≤
      4 * B * x ^ b / T ^ 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    exact mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hD
  have he : (4 * B * x ^ a * Real.pi) / (2 * Real.pi) = 2 * B * x ^ a := by
    field_simp
    ring
  apply hh.trans
  rw [add_div, he]
  linarith only [hside]

theorem MRTWeakHurwitzGrowthInput.riesz_sparse_kernel (h : MRTWeakHurwitzGrowthInput) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
      ∀ u : ℝ, |u| ≤ 2 * Real.exp L →
      ‖mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
        (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => -Real.log (n : ℝ)) u‖ ≤
          C * Y / (1 + u ^ 2) + C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by
  obtain ⟨K, Lr, hK, hb⟩ := h.riesz_boundary
  obtain ⟨D, Tr, hD, hTr, ht⟩ := h.riesz_far_tail
  have he := (mrt_sparse_height_choices (max 2 Tr)).and (eventually_ge_atTop Lr)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp he
  let C := 1000 * (K + D + 1) * (Real.exp 1 + 1)
  refine ⟨C, L₀, by dsimp [C]; positivity, ?_⟩
  intro L Y hL₀' hL hY u hu
  obtain ⟨⟨_, hδ, hT, hU, htail, hside⟩, hLr⟩ := hL₀ L hL₀'
  let x := 4 * Y
  let a := 1 - L ^ (-(3 / 4 : ℝ))
  let b := 1 + 1 / Real.log x
  let T := Real.exp (2 * L)
  let Z := Y / (1 + u ^ 2)
  let E := Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hx : 8 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hb1, hb2, hxb⟩ := mrt_sparse_right_abscissa hx
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith [Real.rpow_pos_of_pos hL0 (-(3 / 4 : ℝ))]
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by positivity
  have huT : |u| ≤ T / 2 := hu.trans hU
  have huT' : |u| < T := by linarith
  obtain ⟨hz, hl, hs⟩ := hb L hLr hL hδ b T u hb1 hb2 hT2
    (by dsimp [T]; linarith [Real.exp_pos (2 * L)]) huT
  have hf := mrt_riesz_finite_shift_simple (by linarith : 1 ≤ x) ha ha1 hb1 hb2 huT'
    (by positivity : 0 ≤ K * L ^ 2) hz hl hs
  have hfar := ht x b T u hx0 hb1 ((le_max_right _ _).trans hT) huT
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I) : ℂ)‖ ≤ 1 := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
    apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hv : ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤
      4 * x / (1 + u ^ 2) + 2 * (K * L ^ 2) * x ^ a +
        4 * (K * L ^ 2) * x ^ b / T ^ 3 + D * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
    have hi := norm_add_le
      ((1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral (mrtZetaRieszIntegrand x u) b (-T) T)
      ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VerticalIntegral (mrtZetaRieszIntegrand x u) b - VIntegral (mrtZetaRieszIntegrand x u) b (-T) T))
    have hid : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral (mrtZetaRieszIntegrand x u) b (-T) T +
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          (VerticalIntegral (mrtZetaRieszIntegrand x u) b - VIntegral (mrtZetaRieszIntegrand x u) b (-T) T) =
        VerticalIntegral' (mrtZetaRieszIntegrand x u) b := by
      simp only [VerticalIntegral', smul_eq_mul]
      ring
    rw [hid] at hi
    have hn := mul_le_mul hnorm hfar (norm_nonneg _) (by positivity)
    have hn' : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VerticalIntegral (mrtZetaRieszIntegrand x u) b -
          VIntegral (mrtZetaRieszIntegrand x u) b (-T) T)‖ ≤
        D * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul]
      simpa only [one_mul] using hn
    exact hi.trans (add_le_add hf hn')
  have hfreq := mrt_sparse_frequency_height hL0.le hu
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hleft : 2 * (K * L ^ 2) * x ^ a ≤ 8 * K * E := by
    have hh := mul_le_mul_of_nonneg_left (mrt_sparse_left_power hL0 hY)
      (show 0 ≤ 2 * (K * L ^ 2) by positivity)
    exact hh.trans_eq (by dsimp [E]; ring)
  have hhor : 4 * (K * L ^ 2) * x ^ b / T ^ 3 ≤ 16 * K * Real.exp 1 * Z := by
    dsimp only [Z]
    rw [← mul_div_assoc]
    rw [hxb]
    apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).mpr
    have hh := (mul_le_mul_of_nonneg_left hfreq (show 0 ≤ L ^ 2 / T ^ 3 by positivity)).trans
      (by simpa [T, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hside)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16 * K * Real.exp 1 * Y by positivity)
    dsimp [x]
    convert hh' using 1 <;> ring
  have hfar' : D * x ^ b * T ^ (-(3 / 2 : ℝ)) ≤ 4 * D * Real.exp 1 * Z := by
    dsimp only [Z]
    rw [← mul_div_assoc]
    rw [hxb]
    apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).mpr
    have hh := (mul_le_mul_of_nonneg_right hfreq (Real.rpow_nonneg hT0.le (-(3 / 2 : ℝ)))).trans htail
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * D * Real.exp 1 * Y by positivity)
    dsimp [x]
    nlinarith only [hh']
  rw [mrt_riesz_prime_kernel_integral (by linarith : 0 < Y) hb1 u, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hp : 4 * x / (1 + u ^ 2) = 16 * Z := by dsimp [x, Z]; ring
  have hv' : ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤
      16 * Z + 8 * K * E + 16 * K * Real.exp 1 * Z + 4 * D * Real.exp 1 * Z :=
    hv.trans (by linarith only [hleft, hhor, hfar', hp])
  have hC1 : 64 + 64 * K * Real.exp 1 + 16 * D * Real.exp 1 ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos 1, mul_nonneg hK.le (Real.exp_pos 1).le,
      mul_nonneg hD.le (Real.exp_pos 1).le]
  have hC2 : 32 * K ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos 1, mul_nonneg hK.le (Real.exp_pos 1).le,
      mul_nonneg hD.le (Real.exp_pos 1).le]
  have hh := add_le_add (mul_le_mul_of_nonneg_right hC1 hZ)
    (mul_le_mul_of_nonneg_right hC2 hE)
  change 4 * ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤ _
  calc
    _ ≤ 4 * (16 * Z + 8 * K * E + 16 * K * Real.exp 1 * Z +
        4 * D * Real.exp 1 * Z) :=
      mul_le_mul_of_nonneg_left hv' (by norm_num : (0 : ℝ) ≤ 4)
    _ = (64 + 64 * K * Real.exp 1 + 16 * D * Real.exp 1) * Z + 32 * K * E := by ring
    _ ≤ C * Z + C * E := hh
    _ = _ := by dsimp [Z, E]; ring

theorem MRTWeakHurwitzGrowthInput.prime_sparse (h : MRTWeakHurwitzGrowthInput) :
    HalaszPrimeSparseInput := by
  obtain ⟨C, L₀, hC, hb⟩ := h.riesz_sparse_kernel
  exact mrt_sparse_prime_of_riesz_kernel ⟨C, L₀, hC, fun L Y hL₀ hL hY _ u hu =>
    hb L Y hL₀ hL hY u hu⟩

end TwoPointCorrelations

end OAI
