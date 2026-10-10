import OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel

namespace OAI

/-! Triangular Perron inversion from Mellin inversion. The triangular
function is a difference of two elementary Mellin transforms. -/

namespace TwoPointCorrelations

open Complex Set MeasureTheory
open scoped Classical

noncomputable def modFiveTriangle (x : ℝ) : ℂ :=
  ((max (1 - x) 0 : ℝ) : ℂ)

lemma modFiveTriangle_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin modFiveTriangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have hd := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hd
  have he : ∀ t ∈ Ioi (0 : ℝ), modFiveTriangle t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [modFiveTriangle, indicator_of_mem hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [modFiveTriangle, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent modFiveTriangle s := by
    exact hd.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin modFiveTriangle s = mellin
        (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
          (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - 1 / (s + 1) := hd.2
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma modFiveTriangle_continuous : Continuous modFiveTriangle := by
  unfold modFiveTriangle
  fun_prop

lemma modFiveTriangle_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin modFiveTriangle) σ := by
  have hi := modFivePerronKernel_integrable (by norm_num : (0 : ℝ) < 1) hσ
  apply hi.congr
  filter_upwards [] with t
  have hs : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using (show 0 < σ by linarith)
  rw [(modFiveTriangle_hasMellin hs).2]
  simp [modFivePerronKernel]

theorem modFivePerron_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = modFiveTriangle (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ modFiveTriangle (one_div_pos.mpr hx)
    (modFiveTriangle_hasMellin (by simpa using hsp)).1
    (modFiveTriangle_verticalIntegrable hσ) (modFiveTriangle_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin modFiveTriangle ((σ : ℂ) + (t : ℂ) * Complex.I) =
          modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (modFiveTriangle_hasMellin (by simpa using hsp)).2]
    unfold modFivePerronKernel
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

lemma modFivePerron_gt_one {x σ : ℝ} (hx : 1 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 1 - 1 / (x : ℂ) := by
  rw [modFivePerron_inversion (zero_lt_one.trans hx) hσ]
  have hi : (1 : ℝ) / x ≤ 1 := (div_le_one (zero_lt_one.trans hx)).mpr hx.le
  rw [modFiveTriangle, max_eq_left (sub_nonneg.mpr hi)]
  push_cast
  rfl

lemma modFivePerron_lt_one {x σ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 0 := by
  rw [modFivePerron_inversion hx hσ]
  have hi : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa using hx1.le)
  rw [modFiveTriangle, max_eq_right (sub_nonpos.mpr hi)]
  rfl

end TwoPointCorrelations

end OAI
