import OAI.NumberTheory.CubicMoment.Estimates.MellinContour
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma logPullback_compact (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) :
    HasCompactSupport (fun u : ℝ => W (Real.exp (-u))) := by
  have hc : IsCompact ((fun x : ℝ => -Real.log x) '' tsupport W) :=
    hW.isCompact.image_of_continuousOn
      (Real.continuousOn_log.neg.mono (fun x hx => ne_of_gt (hpos hx)))
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro u hu
  refine ⟨Real.exp (-u), subset_tsupport W hu, ?_⟩
  simp

def mellinLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) : 𝓢(ℝ,ℂ) :=
  ((logPullback_compact W hW hpos).smul_left
    (f := fun u : ℝ => Real.exp (-σ*u))).toSchwartzMap
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul
      (hsm.comp (Real.contDiff_exp.comp contDiff_id.neg)))

lemma mellinLogSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ u : ℝ) :
    mellinLogSchwartz W hW hpos hsm σ u = Real.exp (-σ*u) • W (Real.exp (-u)) := rfl

lemma mellin_frequency_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ t : ℝ, ‖t‖ ≤ C*(1+‖t/(2*Real.pi)‖)^k := by
  refine ⟨1,2*Real.pi,?_⟩
  intro t
  rw [pow_one, norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have hp : 0 < 2*Real.pi := by positivity
  calc
    ‖t‖ = (2*Real.pi) * (‖t‖/(2*Real.pi)) := by field_simp
    _ ≤ _ := by gcongr; linarith

def mellinVerticalSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLM ℂ (by
    simp only [div_eq_mul_inv]
    fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
    mellin_frequency_growth (𝓕 (mellinLogSchwartz W hW hpos hsm σ))

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

theorem smooth_mellin_vertical_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  let F := mellinVerticalSchwartz W hW hpos hsm σ
  let C := 2^A * (Finset.Iic (A,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro t
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl F t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  rw [← mellinVerticalSchwartz_apply W hW hpos hsm σ t]
  exact hb.trans (by dsimp [C]; linarith)

private lemma smooth_mellin_power_bounds (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (a b : ℝ) :
    W =O[atTop] (fun x : ℝ => x^(-a)) ∧
      W =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x^(-b)) := by
  have ht : W =ᶠ[atTop] 0 := by
    have h := hasCompactSupport_iff_eventuallyEq.mp hW
    rw [Filter.coclosedCompact_eq_cocompact] at h
    exact h.filter_mono atTop_le_cocompact
  have h0 : (0 : ℝ) ∉ tsupport W := fun h =>
    (lt_irrefl (0 : ℝ)) (Set.mem_Ioi.mp (hpos h))
  have hb : W =ᶠ[𝓝[>] (0 : ℝ)] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp h0).filter_mono nhdsWithin_le_nhds
  exact ⟨(isBigO_zero _ _).congr' ht.symm Filter.EventuallyEq.rfl,
    (isBigO_zero _ _).congr' hb.symm Filter.EventuallyEq.rfl⟩

theorem smooth_mellin_convergent (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hc : Continuous W) (s : ℂ) :
    MellinConvergent W s := by
  obtain ⟨ht,hb⟩ := smooth_mellin_power_bounds W hW hpos (s.re+1) (s.re-1)
  exact mellinConvergent_of_isBigO_rpow (hc.locallyIntegrable.locallyIntegrableOn _)
    ht (by linarith) hb (by linarith)

theorem smooth_mellin_entire (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hc : Continuous W) : Differentiable ℂ (mellin W) := by
  intro s
  obtain ⟨ht,hb⟩ := smooth_mellin_power_bounds W hW hpos (s.re+1) (s.re-1)
  exact mellin_differentiableAt_of_isBigO_rpow (hc.locallyIntegrable.locallyIntegrableOn _)
    ht (by linarith) hb (by linarith)

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
