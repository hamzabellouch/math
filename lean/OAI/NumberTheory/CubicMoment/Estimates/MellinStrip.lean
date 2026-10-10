import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! Uniform rapid Mellin decay on a fixed closed real strip. The bound
comes from the actual compact logarithmic support, not an additional
analytic input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

private lemma exp_linear_deriv_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| * |u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

private lemma mellinLogSchwartz_eq_smul (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ) =
      fun u => Real.exp (-σ*u) • mellinLogSchwartz W hW hpos hsm 0 u := by
  ext u
  simp [mellinLogSchwartz_apply]

theorem mellinLogSchwartz_seminorm_uniform (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤ C := by
  let G := mellinLogSchwartz W hW hpos hsm 0
  obtain ⟨R₀,hR₀⟩ := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := max R₀ 1
  let M' := max M 0
  let B := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (M'^i * Real.exp (M'*R)) * SchwartzMap.seminorm ℝ 0 (n-i) G
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hM : 0 ≤ M' := le_max_right _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by positivity)
  refine ⟨R^k*B, by positivity, ?_⟩
  intro σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hg (i : ℕ) : ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ B := by
      rw [mellinLogSchwartz_eq_smul W hW hpos hsm σ]
      apply hd.trans
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (exp_linear_deriv_bound hM (hσ.trans (le_max_left _ _)) hu i) (by positivity)
      · exact hg (n-i)
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |u|) hu k) hb
        (by positivity) (by positivity)
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      have hb : |u| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ u hs'
      exact hu (hb.trans (le_max_left _ _))
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_family_bounded (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun σ => mellinVerticalSchwartz W hW hpos hsm σ) '' {σ | |σ| ≤ M}) := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun σ => mellinLogSchwartz W hW hpos hsm σ
  have hb : Bornology.IsVonNBounded ℝ (f '' {σ | |σ| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,h⟩ := mellinLogSchwartz_seminorm_uniform W hW hpos hsm M i.1 i.2
    exact ⟨C+1,by linarith,fun σ hσ => (h σ hσ).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  rw [← Set.image_comp]
  rfl

theorem smooth_mellin_strip_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  have hb := mellinVertical_family_bounded W hW hpos hsm M
  obtain ⟨C,hC,h⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun σ => mellinVerticalSchwartz W hW hpos hsm σ) |>.mp hb (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (h σ hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
