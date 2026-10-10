import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularHecke
import OAI.NumberTheory.CubicMoment.Angular.AngularDualContour

namespace OAI

/-! Exact retained-plus-tail decomposition for a fixed angular Hecke
series. The possible poles of the totalized Gamma denominator are handled
using the entire completion, before any integration is performed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angular_left_uncompleted (χ χdual : EisensteinIdealExponent → ℂ)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    let u : ℂ := s-(t:ℂ)*Complex.I
    L u = ε*(A:ℂ)^(1-2*u)*angularGammaFEQuotient k u*
      normDirichletSeries χdual idealExponentNorm (1-u) := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
  have hr : 1 < (1-u).re := by
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  by_cases hGu : Complex.Gamma (u+(k:ℂ)) = 0
  · obtain ⟨Λ,hΛ,heq,-⟩ := hcomp
    have hdec := shifted_completed_hecke_decompletion hA data.entire.continuous hΛ.continuous heq
    have hzero : L u = 0 := by
      rw [congrFun hdec u,hGu,inv_zero,mul_zero,zero_mul]
    change L u = _
    rw [hzero,angularGammaFEQuotient,hGu,div_zero,mul_zero,zero_mul]
  have hGd : Complex.Gamma (1-u+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  have hf := hecke_uncompleted hA data.functional_equation u hGu hGd
  rw [data.dual_right_series _ hr] at hf
  exact hf

lemma angular_left_integrand_split (χ χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (W : ℝ → ℂ) (Z J : ℝ) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I) =
      mellin W s*(Z:ℂ)^s*angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm
        ε A k (s-(t:ℂ)*Complex.I) + angularDualTailIntegrand W χdual ε A Z J k m t τ := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hr : 1 < (1-u).re := by
    have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [angular_left_uncompleted χ χdual hA hk data hcomp hm t τ,
    idealDirichlet_split χdual hχdual (1-u) hr J]
  dsimp [angularFiniteHeckeDual,angularDualTailIntegrand,angularGammaFEQuotient,u]
  ring

lemma angular_finite_dual_mellin_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {A b σ Z k : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hZ : 1 ≤ Z)
    (hσ : σ ∈ Icc b (1/2:ℝ)) (hGamma : AngularGammaQuotientStripBound k b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    Integrable (fun τ : ℝ => mellin W (σ+(τ:ℂ)*Complex.I)*
      (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*angularFiniteHeckeDual S a N ε A k
        (σ+((τ-t:ℝ):ℂ)*Complex.I)) := by
  obtain ⟨C,n,hC,hbound⟩ := angular_finite_dual_strip_growth S a N hN ε hk hA hGamma
  apply mellinHecke_line_integrable W hW hpos hsm hZ σ t _ _ hC n
    (fun τ => hbound σ hσ (τ-t))
  apply (differentiableOn_angularFiniteHeckeDual S a N
    (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hk hA).continuousOn.comp_continuous
    (by fun_prop)
  intro τ
  change ((σ:ℂ)+((τ-t:ℝ):ℂ)*Complex.I).re < 1
  simpa using lt_of_le_of_lt hσ.2 (by norm_num : (1/2:ℝ) < 1)

theorem angular_smooth_truncated_identity
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z)
    {m : ℕ} (hm : 2 ≤ m) (J t : ℝ)
    (hGamma : AngularGammaQuotientStripBound k (1/2-(m:ℝ))) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*
        ((∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A k
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) +
        ∫ τ : ℝ, angularDualTailIntegrand W χdual ε A Z J k m t τ) := by
  let σ : ℝ := 1/2-(m:ℝ)
  let F (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*L (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let D (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*angularFiniteHeckeDual (fullIdealBall J) χdual
      idealExponentNorm ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let E (τ : ℝ) : ℂ := angularDualTailIntegrand W χdual ε A Z J k m t τ
  have hσ : σ ≤ 1/2 := by
    dsimp [σ]
    have hmr : (0:ℝ) ≤ m := by positivity
    linarith
  have hsplit (τ : ℝ) : F τ = D τ+E τ := by
    have h := angular_left_integrand_split χ χdual hχdual hA hk data hcomp W Z J hm t τ
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
  have hDi : Integrable D := angular_finite_dual_mellin_integrable (fullIdealBall J)
    χdual idealExponentNorm (fun ν _ => idealExponentNorm_ge_one ν) ε hk hA hZ
    ⟨le_rfl,hσ⟩ hGamma W hW hpos hsm t
  have hEi : Integrable E := (hFi.sub hDi).congr (Filter.Eventually.of_forall (fun τ => by
    have h := hsplit τ
    change F τ-D τ = E τ
    linear_combination h))
  have hi : (∫ τ : ℝ, F τ) = (∫ τ : ℝ, D τ)+(∫ τ : ℝ, E τ) := by
    calc
      _ = ∫ τ : ℝ, D τ+E τ := integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = _ := integral_add hDi hEi
  have hmell := angular_hecke_smooth_mellin_left χ χdual hχ data W hW hpos hsm hZ m t
  change (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F τ) at hmell
  rw [hmell,hi]
  have hmove := angular_finite_dual_contour_shift (fullIdealBall J) χdual idealExponentNorm
    (fun ν _ => idealExponentNorm_ge_one ν) ε hk hA hZ hσ hGamma W hW hpos hsm t
  change (∫ τ : ℝ, D τ) = _ at hmove
  rw [hmove]


end CubicFirstMoment

end

end OAI
