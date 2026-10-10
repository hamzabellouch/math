import OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronInversion

namespace OAI

/-! A positive quadratic Riesz weight and its exact Mellin kernel. The
third denominator gives the additional decay needed by sparse prime duality. -/

namespace TwoPointCorrelations

open Complex Set MeasureTheory
open scoped Classical

noncomputable def mrtRieszSquare (x : ℝ) : ℂ :=
  (((max (1 - x) 0) ^ 2 : ℝ) : ℂ)

noncomputable def mrtRieszKernel (x : ℝ) (s : ℂ) : ℂ :=
  2 * (x : ℂ) ^ s / (s * (s + 1) * (s + 2))

lemma mrt_riesz_square_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin mrtRieszSquare s (2 / (s * (s + 1) * (s + 2))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have h2 := hasMellin_cpow_Ioc (2 : ℂ) (s := s) (by simpa using (show 0 < s.re + 2 by linarith))
  have h11 := hasMellin_add h1.1 h1.1
  have hd := hasMellin_sub h0.1 h11.1
  have hf := hasMellin_add hd.1 h2.1
  have he : ∀ t ∈ Ioi (0 : ℝ), mrtRieszSquare t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        ((Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t +
         (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) +
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (2 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp only [mrtRieszSquare, max_eq_left (sub_nonneg.mpr ht1), indicator_of_mem hm,
        Complex.cpow_one, Complex.cpow_ofNat, Complex.ofReal_pow, Complex.ofReal_sub,
        Complex.ofReal_one]
      ring
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [mrtRieszSquare, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent mrtRieszSquare s :=
    hf.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin mrtRieszSquare s = mellin (fun t =>
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        ((Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t +
         (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) +
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (2 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - (1 / (s + 1) + 1 / (s + 1)) + 1 / (s + 2) := by
      rw [hf.2, hd.2, h11.2, h0.2, h1.2, h2.2]
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      have hs2 : s + 2 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma mrt_riesz_square_continuous : Continuous mrtRieszSquare := by
  unfold mrtRieszSquare
  fun_prop

lemma mrt_riesz_kernel_factor (x : ℝ) (s : ℂ) :
    mrtRieszKernel x s = modFivePerronKernel x s * (2 / (s + 2)) := by
  unfold mrtRieszKernel modFivePerronKernel
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma mrt_riesz_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * x ^ σ / (1 + t ^ 2) := by
  have hl : (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖ := by
    have hh := Complex.re_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + 2)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, zero_mul, mul_zero, sub_self, add_zero] at hh
    norm_num at hh
    linarith
  have hf : ‖(2 : ℂ) / ((σ : ℂ) + (t : ℂ) * Complex.I + 2)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by linarith)).mpr hl
  rw [mrt_riesz_kernel_factor, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hf).trans
    (modFive_perron_kernel_vertical hx hσ t)

lemma mrt_riesz_kernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h2 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 2 ≠ 0 := by
    intro t he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  have hc : Continuous (fun t : ℝ => mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    simp only [mrt_riesz_kernel_factor]
    apply Continuous.mul
    · unfold modFivePerronKernel
      apply Continuous.div
      · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
          fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      · fun_prop
      · intro t
        apply mul_ne_zero
        · intro he
          have hh := congrArg Complex.re he
          norm_num at hh
          linarith
        · intro he
          have hh := congrArg Complex.re he
          norm_num at hh
          linarith
    · exact continuous_const.div (by fun_prop) h2
  have hm : Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  exact hm.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (mrt_riesz_kernel_vertical hx hσ))

lemma mrt_riesz_square_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin mrtRieszSquare) σ := by
  apply (mrt_riesz_kernel_integrable (by norm_num : (0 : ℝ) < 1) hσ).congr
  filter_upwards [] with t
  have hs : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simpa using (show 0 < σ by linarith)
  rw [(mrt_riesz_square_hasMellin hs).2]
  simp [mrtRieszKernel]

theorem mrt_riesz_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (mrtRieszKernel x) σ = mrtRieszSquare (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ mrtRieszSquare (one_div_pos.mpr hx)
    (mrt_riesz_square_hasMellin (by simpa using hsp)).1
    (mrt_riesz_square_verticalIntegrable hσ) (mrt_riesz_square_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin mrtRieszSquare ((σ : ℂ) + (t : ℂ) * Complex.I) =
          mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (mrt_riesz_square_hasMellin (by simpa using hsp)).2]
    unfold mrtRieszKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm

end TwoPointCorrelations

end OAI
