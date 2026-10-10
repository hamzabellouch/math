import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHomotopyCount

namespace OAI

/-! # The outgoing normalization preserves zero multiplicities -/

open Filter Topology

namespace DefocusingNLS

attribute [local irreducible] matchingHomotopyColumn normalizedMatchingC slowBoundaryColumn

theorem analyticAt_matchingColumnDeterminant {u v : ℂ → Fin 2 → ℂ} {z : ℂ}
    (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z) :
    AnalyticAt ℂ (fun w => matchingColumnDeterminant (u w) (v w)) z := by
  have h := (((analyticAt_pi_iff.mp hu) 0).mul ((analyticAt_pi_iff.mp hv) 1)).sub
    (((analyticAt_pi_iff.mp hu) 1).mul ((analyticAt_pi_iff.mp hv) 0))
  convert! h using 1

noncomputable def spectralSlowDeterminant (ell : ℕ) (b Z : ℝ) (z : ℂ) : ℂ :=
  matchingColumnDeterminant
    (slowBoundaryColumn (spectralQ ell 1 b z) (ell + 6) (Complex.I * Z))
    (slowBoundaryColumn (spectralQ ell (-1) b z) (ell + 6) (-Complex.I * Z))

noncomputable def spectralTailNormalization (ell : ℕ) (h b Z : ℝ) (z : ℂ) : ℂ :=
  (normalizedMatchingC (spectralQ ell h b z) (ell + 6) ((h : ℂ) * Complex.I * Z) 8)⁻¹

theorem spectralTailNormalization_analytic_ne_zero (ell : ℕ) (h b Z : ℝ) (z : ℂ)
    (hh : h ≠ 0) (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    AnalyticAt ℂ (spectralTailNormalization ell h b Z) z ∧
      spectralTailNormalization ell h b Z z ≠ 0 := by
  have hq : -(1 / 32 : ℝ) ≤ (spectralQ ell h b z).re - (ell : ℝ) / 2 := by
    rw [spectralQ_re]
    linarith
  have h := analyticAt_matchingTailScalar ell 8 ((h : ℂ) * Complex.I * Z)
    (spectralQ ell h b z) (by decide) hq (by simp) (by simpa using mul_ne_zero hh hZ)
  exact ⟨h.1.comp (analyticAt_spectralQ ell _ b z), h.2⟩

theorem analyticAt_spectralSlowColumn (ell : ℕ) (h b Z : ℝ) (z : ℂ)
    (hh : h ≠ 0) (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    AnalyticAt ℂ (fun w => slowBoundaryColumn (spectralQ ell h b w) (ell + 6)
      ((h : ℂ) * Complex.I * Z)) z := by
  have hq : -1 < (spectralQ ell h b z).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  exact ((analyticOnNhd_slowBoundaryColumn (ell + 6) ((h : ℂ) * Complex.I * Z)
    (by simp) (by simpa using mul_ne_zero hh hZ)) _ hq).comp
      (analyticAt_spectralQ ell h b z)

theorem analyticAt_spectralSlowDeterminant (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    AnalyticAt ℂ (spectralSlowDeterminant ell b Z) z := by
  have hp := analyticAt_spectralSlowColumn ell 1 b Z z (by norm_num) hZ hz
  have hm := analyticAt_spectralSlowColumn ell (-1) b Z z (by norm_num) hZ hz
  have hd := analyticAt_matchingColumnDeterminant hp hm
  unfold spectralSlowDeterminant
  simpa only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul] using hd

theorem spectralHomotopy_endpoint_factor (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    spectralHomotopyDeterminant ell b Z 1 z =
      (spectralTailNormalization ell 1 b Z z * spectralTailNormalization ell (-1) b Z z) *
        spectralSlowDeterminant ell b Z z := by
  have he : ell + 5 + 1 = ell + 6 := by omega
  have hq (h : ℝ) : -1 < (spectralQ ell h b z).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hp : normalizedMatchingC (spectralQ ell 1 b z) (ell + 6)
      ((1 : ℂ) * Complex.I * Z) 8 ≠ 0 := by
    intro h
    have hn := (spectralTailNormalization_analytic_ne_zero ell 1 b Z z
      (by norm_num) hZ hz).2
    exact hn (by simp only [spectralTailNormalization, Complex.ofReal_one, h, inv_zero])
  have hm : normalizedMatchingC (spectralQ ell (-1) b z) (ell + 6)
      ((-1 : ℂ) * Complex.I * Z) 8 ≠ 0 := by
    intro h
    have hn := (spectralTailNormalization_analytic_ne_zero ell (-1) b Z z
      (by norm_num) hZ hz).2
    exact hn (by simp only [spectralTailNormalization, Complex.ofReal_neg,
      Complex.ofReal_one, h, inv_zero])
  simp only [one_mul, neg_one_mul] at hp hm
  unfold spectralHomotopyDeterminant
  rw [matchingHomotopyColumn_one (ell + 5) 8 (Complex.I * Z)
    (spectralQ ell 1 b z) (by decide) (hq 1) (by simp) (by simpa using hZ)
    (by simpa only [he] using hp)]
  rw [matchingHomotopyColumn_one (ell + 5) 8 (-Complex.I * Z)
    (spectralQ ell (-1) b z) (by decide) (hq (-1)) (by simp) (by simpa using hZ)
    (by simpa only [he] using hm), matchingColumnDeterminant_smul]
  simp only [spectralSlowDeterminant, spectralTailNormalization, he,
    Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]

theorem analyticOrderAt_spectralHomotopy_endpoint (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) < z.re) :
    analyticOrderAt (spectralHomotopyDeterminant ell b Z 1) z =
      analyticOrderAt (spectralSlowDeterminant ell b Z) z := by
  let a : ℂ → ℂ := fun w =>
    spectralTailNormalization ell 1 b Z w * spectralTailNormalization ell (-1) b Z w
  have hp := spectralTailNormalization_analytic_ne_zero ell 1 b Z z (by norm_num) hZ hz.le
  have hm := spectralTailNormalization_analytic_ne_zero ell (-1) b Z z (by norm_num) hZ hz.le
  have ha : AnalyticAt ℂ a z := hp.1.mul hm.1
  have han : a z ≠ 0 := mul_ne_zero hp.2 hm.2
  have hf := analyticAt_spectralSlowDeterminant ell b Z z hZ hz.le
  have he : spectralHomotopyDeterminant ell b Z 1 =ᶠ[𝓝 z]
      a * spectralSlowDeterminant ell b Z := by
    have hre := Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hz)
    filter_upwards [hre] with w hw
    exact spectralHomotopy_endpoint_factor ell b Z w hZ hw.le
  rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hf,
    ha.analyticOrderAt_eq_zero.mpr han, zero_add]

theorem rectangleZeroCount_spectralHomotopy_endpoint (ell : ℕ) (b Z V : ℝ)
    (hZ : Z ≠ 0) :
    rectangleZeroCount V (spectralHomotopyDeterminant ell b Z 1) =
      rectangleZeroCount V (spectralSlowDeterminant ell b Z) := by
  unfold rectangleZeroCount
  apply tsum_congr
  intro z
  exact analyticOrderAt_spectralHomotopy_endpoint ell b Z z hZ z.2.1

theorem exists_spectral_rectangle_outgoing_count (hR : RectangleRouche) (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ b Z : ℝ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      rectangleZeroCount V (spectralHomotopyDeterminant ell b Z 0) =
        rectangleZeroCount V (spectralSlowDeterminant ell b Z) := by
  obtain ⟨V, hV, hc⟩ := exists_spectral_rectangle_homotopy_count hR ell
  refine ⟨V, hV, ?_⟩
  intro b Z hb hZ
  have hZ0 : Z ≠ 0 := by intro h; norm_num [h] at hZ
  exact (hc b Z hb hZ).trans (rectangleZeroCount_spectralHomotopy_endpoint ell b Z V hZ0)

end DefocusingNLS

end OAI
