import OAI.NumberTheory.CubicMoment.Estimates.HeckeSmoothDual

namespace OAI

/-! The finite dual part plus an explicit, arbitrarily small tail. All
sum-integral and contour operations are justified before using the
symmetry line in a character average. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem hecke_smooth_truncated_identity
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : PrimitiveHeckeAnalyticData χ χdual A ε L Ldual)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z)
    {m : ℕ} (hm : 2 ≤ m) (J t : ℝ)
    (hGamma : GammaQuotientStripBound (1/2-(m:ℝ))) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*
        ((∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          finiteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) +
        ∫ τ : ℝ, heckeDualTailIntegrand W χdual ε A Z J m t τ) := by
  let σ : ℝ := 1/2-(m:ℝ)
  let F (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*L (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let D (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*finiteHeckeDual (fullIdealBall J) χdual
      idealExponentNorm ε A (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let E (τ : ℝ) : ℂ := heckeDualTailIntegrand W χdual ε A Z J m t τ
  have hσ : σ ≤ 1/2 := by
    dsimp [σ]
    have hmr : (0:ℝ) ≤ m := by positivity
    linarith
  have hsplit (τ : ℝ) : F τ = D τ+E τ := by
    have h := hecke_left_integrand_split χ χdual hχdual hA data W Z J hm t τ
    dsimp only at h
    have hs : ((σ:ℝ):ℂ)+(τ:ℂ)*Complex.I =
        (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I := by dsimp [σ]; push_cast; ring
    have hu : (σ:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I =
        (σ:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [← hs,hu] at h
    exact h
  obtain ⟨C,n,hC,hgrowth⟩ := data.strip_growth m
  have hFi : Integrable F := by
    apply mellinHecke_line_integrable W hW hpos hsm hZ σ t L
      (data.entire.continuous.comp (by fun_prop)) hC n
    intro τ
    exact hgrowth σ ⟨le_rfl,hσ.trans (by norm_num)⟩ (τ-t)
  have hDi : Integrable D := finite_hecke_dual_mellin_integrable (fullIdealBall J)
    χdual idealExponentNorm (fun ν _ => idealExponentNorm_ge_one ν) ε hA hZ
    ⟨le_rfl,hσ⟩ hGamma W hW hpos hsm t
  have hEi : Integrable E := (hFi.sub hDi).congr (Filter.Eventually.of_forall (fun τ => by
    have h := hsplit τ
    change F τ-D τ = E τ
    linear_combination h))
  have hi : (∫ τ : ℝ, F τ) = (∫ τ : ℝ, D τ)+(∫ τ : ℝ, E τ) := by
    calc
      _ = ∫ τ : ℝ, D τ+E τ := integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = _ := integral_add hDi hEi
  have hmell := hecke_smooth_mellin_left χ χdual hχ data W hW hpos hsm hZ m t
  change (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F τ) at hmell
  rw [hmell,hi]
  have hmove := finite_hecke_dual_contour_shift (fullIdealBall J) χdual idealExponentNorm
    (fun ν _ => idealExponentNorm_ge_one ν) ε hA hZ hσ hGamma W hW hpos hsm t
  change (∫ τ : ℝ, D τ) = _ at hmove
  rw [hmove]

lemma finite_hecke_dual_symmetry_integrand {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (ε : ℂ) {A Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (G : ℂ → ℂ) (t τ : ℝ) :
    G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S a N ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
    (Real.sqrt Z:ℂ)*G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      heckeSymmetryFactor ε (A^2) Z 0 t τ *
      finiteNormDirichlet S a N ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I) := by
  unfold finiteHeckeDual gammaFEQuotient
  rw [hecke_scale_phase hZ,hecke_conductor_phase hA]
  have hu : 1-((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
      (1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by ring
  rw [hu]
  unfold heckeSymmetryFactor heckeGammaRatio
  norm_num only [zero_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

end CubicFirstMoment

end

end OAI
