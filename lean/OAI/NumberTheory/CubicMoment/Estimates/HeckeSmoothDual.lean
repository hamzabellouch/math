import OAI.NumberTheory.CubicMoment.Estimates.DualPolynomialScale
import OAI.NumberTheory.CubicMoment.Estimates.DualTailTruncation
import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

/-- The precise ordinary Hecke inputs needed for contour shifting:
right-half-plane series, entireness, the regular-point functional equation,
and polynomial growth in each of the required strips. See Watkins (2011)
§3.6 and Thorner--Zaman (2019) §2C. The strip-growth bound follows from the completed finite-order property and
weak reciprocal-Gamma growth by the Phragmén–Lindelöf theorem. -/
structure PrimitiveHeckeAnalyticData (χ χdual : EisensteinIdealExponent → ℂ)
    (A : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A 0 ε L Ldual
  strip_growth : ∀ m : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧
    ∀ σ ∈ Icc (1/2-(m:ℝ)) 2, ∀ u : ℝ,
      ‖L (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^n

lemma mellinPhase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    mellinPhase t x = (x:ℂ)^((t:ℂ)*Complex.I) := by
  simpa only [Complex.ofReal_zero,zero_add,Real.rpow_zero,Complex.ofReal_one,one_mul]
    using (positive_cpow_phase hx 0 t).symm

lemma twisted_normDirichletSeries (χ : EisensteinIdealExponent → ℂ) (t : ℝ) (s : ℂ) :
    normDirichletSeries (fun ν => χ ν*mellinPhase t (idealExponentNorm ν)) idealExponentNorm s =
      normDirichletSeries χ idealExponentNorm (s-(t:ℂ)*Complex.I) := by
  apply tsum_congr
  intro ν
  dsimp only
  rw [mellinPhase_eq_cpow (idealExponentNorm_pos ν),mul_assoc,← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne')]
  congr 2
  ring

/-- Exact Mellin inversion for the actual norm-twisted complete ideal sum. -/
theorem hecke_twisted_smooth_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (2+(τ:ℂ)*Complex.I)*(Z:ℂ)^(2+(τ:ℂ)*Complex.I)*
          L (2+((τ-t:ℝ):ℂ)*Complex.I) := by
  have h := ideal_smooth_mellin (fun ν => χ ν*mellinPhase t (idealExponentNorm ν))
    (by intro ν; simpa only [norm_mul,mellinPhase_norm,mul_one] using hχ ν)
    W hW hpos hsm (by norm_num : (1:ℝ) < 2) hZ
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  rw [twisted_normDirichletSeries]
  have he : ((2:ℂ)+(τ:ℂ)*Complex.I)-(t:ℂ)*Complex.I =
      2+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  norm_num only [Complex.ofReal_ofNat]
  rw [he,hL _ (by simp)]

lemma summable_idealDirichlet (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
  apply Summable.of_norm
  have hn (ν : EisensteinIdealExponent) :
      ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ = ‖χ ν‖*idealExponentNorm ν^(-s.re) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  simpa only [hn] using summable_ideal_character_weight hs χ hχ

lemma idealDirichlet_split (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) (J : ℝ) :
    normDirichletSeries χ idealExponentNorm s =
      finiteNormDirichlet (fullIdealBall J) χ idealExponentNorm s + idealDirichletTail χ J s := by
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  have hf : Summable f := summable_idealDirichlet χ hχ s hs
  have hhead : Summable (fun ν => if idealExponentNorm ν ≤ J then f ν else 0) :=
    hf.indicator _
  have htail : Summable (fun ν => if J < idealExponentNorm ν then f ν else 0) :=
    hf.indicator _
  have hfinite : (∑' ν, if idealExponentNorm ν ≤ J then f ν else 0) =
      ∑ ν ∈ fullIdealBall J, f ν := by
    calc
      _ = ∑ ν ∈ fullIdealBall J, if idealExponentNorm ν ≤ J then f ν else 0 := by
        apply tsum_eq_sum
        intro ν hν
        simp only [mem_fullIdealBall] at hν
        simp [hν]
      _ = _ := Finset.sum_congr rfl (fun ν hν => ite_eq_left (mem_fullIdealBall.mp hν))
  calc
    _ = ∑' ν, ((if idealExponentNorm ν ≤ J then f ν else 0) +
        (if J < idealExponentNorm ν then f ν else 0)) := by
      apply tsum_congr
      intro ν
      by_cases hν : idealExponentNorm ν ≤ J <;> simp [hν,not_lt_of_ge,lt_of_not_ge,f]
    _ = (∑' ν, if idealExponentNorm ν ≤ J then f ν else 0) +
        ∑' ν, if J < idealExponentNorm ν then f ν else 0 := hhead.tsum_add htail
    _ = _ := by rw [hfinite]; rfl

/-- The original smooth sum on a far-left line, with the contour move
justified by the ordinary analytic strip properties. -/
theorem hecke_smooth_mellin_left (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A : ℝ} {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : PrimitiveHeckeAnalyticData χ χdual A ε L Ldual)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z) (m : ℕ) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^(((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          L (((1/2-(m:ℝ)):ℝ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨C,n,hC,hgrowth⟩ := data.strip_growth m
  have hshift := mellinHecke_contour_shift W hW hpos hsm
    (show 1/2-(m:ℝ) ≤ 2 by
      have hmr : (0:ℝ) ≤ m := by positivity
      linarith)
    hZ t L data.entire hC n (by intro σ hσ τ; exact hgrowth σ hσ (τ-t))
  norm_num only [Complex.ofReal_ofNat] at hshift
  rw [hecke_twisted_smooth_mellin χ hχ L data.right_series W hW hpos hsm
    (lt_of_lt_of_le zero_lt_one hZ) t,← hshift]

lemma hecke_left_uncompleted (χ χdual : EisensteinIdealExponent → ℂ)
    {A : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : PrimitiveHeckeAnalyticData χ χdual A ε L Ldual)
    {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    let u : ℂ := s-(t:ℂ)*Complex.I
    L u = ε*(A:ℂ)^(1-2*u)*gammaFEQuotient u*
      normDirichletSeries χdual idealExponentNorm (1-u) := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have he : u = (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by
    dsimp [u]
    push_cast
    ring
  have hGu : Complex.Gamma (u+(0:ℂ)) ≠ 0 := by
    rw [add_zero,he]
    exact Complex.Gamma_ne_zero (half_sub_nat_regular m (τ-t))
  have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
  have hr : 1 < (1-u).re := by
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hGd : Complex.Gamma (1-u+(0:ℂ)) ≠ 0 := by
    rw [add_zero]
    exact Complex.Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hr)
  have hf := hecke_uncompleted hA data.functional_equation u hGu hGd
  simp only [Complex.ofReal_zero,add_zero] at hf
  rw [data.dual_right_series _ hr] at hf
  exact hf

/-- Exact retained-plus-tail decomposition before the finite contour
move. Both terms are derived from the complete ideal series. -/
lemma hecke_left_integrand_split (χ χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A : ℝ} (hA : 0 < A)
    {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : PrimitiveHeckeAnalyticData χ χdual A ε L Ldual)
    (W : ℝ → ℂ) (Z J : ℝ) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I) =
      mellin W s*(Z:ℂ)^s*finiteHeckeDual (fullIdealBall J) χdual idealExponentNorm
        ε A (s-(t:ℂ)*Complex.I) + heckeDualTailIntegrand W χdual ε A Z J m t τ := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hr : 1 < (1-u).re := by
    have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [hecke_left_uncompleted χ χdual hA data hm t τ,
    idealDirichlet_split χdual hχdual (1-u) hr J]
  dsimp [finiteHeckeDual,heckeDualTailIntegrand,gammaFEQuotient,u]
  ring

lemma mellinHecke_line_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 1 ≤ Z) (σ t : ℝ) (L : ℂ → ℂ)
    (hcont : Continuous (fun τ : ℝ => L (σ+((τ-t:ℝ):ℂ)*Complex.I)))
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hbound : ∀ τ : ℝ, ‖L (σ+((τ-t:ℝ):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^n) :
    Integrable (fun τ : ℝ => mellin W (σ+(τ:ℂ)*Complex.I)*
      (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*L (σ+((τ-t:ℝ):ℂ)*Complex.I)) := by
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hZ).ne'⟩
  have hs : Continuous (fun τ : ℝ => (σ:ℂ)+(τ:ℂ)*Complex.I) := by fun_prop
  have hc := (((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs).mul
    ((differentiable_const_cpow_of_neZero (Z:ℂ)).continuous.comp hs)).mul hcont
  obtain ⟨K,_,hK⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t L hC n
    (a := σ) (b := σ) (by intro x hx τ; have he : x = σ := le_antisymm hx.2 hx.1; subst x; exact hbound τ)
  exact (mellinEdgeMajorant_integrable K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (hK σ ⟨le_rfl,le_rfl⟩))

lemma finite_hecke_dual_mellin_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {A b σ Z : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z)
    (hσ : σ ∈ Icc b (1/2:ℝ)) (hGamma : GammaQuotientStripBound b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    Integrable (fun τ : ℝ => mellin W (σ+(τ:ℂ)*Complex.I)*
      (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*finiteHeckeDual S a N ε A (σ+((τ-t:ℝ):ℂ)*Complex.I)) := by
  obtain ⟨C,n,hC,hbound⟩ := finite_hecke_dual_strip_growth S a N hN ε hA hGamma
  apply mellinHecke_line_integrable W hW hpos hsm hZ σ t _ _ hC n
    (fun τ => hbound σ hσ (τ-t))
  apply (differentiableOn_finiteHeckeDual S a N
    (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hA).continuousOn.comp_continuous
    (by fun_prop)
  intro τ
  change ((σ:ℂ)+((τ-t:ℝ):ℂ)*Complex.I).re < 1
  simpa using lt_of_le_of_lt hσ.2 (by norm_num : (1/2:ℝ) < 1)

end CubicFirstMoment

end

end OAI
