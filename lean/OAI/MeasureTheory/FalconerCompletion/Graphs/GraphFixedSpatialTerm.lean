import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.RadialPhaseIntegral
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def graphFixedSpatialTermND (Ψ : ℝ → ℂ) (Q : ℝ)
    (e₁ e₂ : V) (b₁ b₂ : V → ℂ) : ℂ :=
  ∫ u : ℝ, Ψ u*sphereAxisIntegralND (Q*u) e₁ b₁*sphereAxisIntegralND (Q*u) e₂ b₂

lemma canonicalSphereMeasureND_prod_ae_norm :
    ∀ᵐ z : V×V ∂(canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V),
      ‖z.1‖=1 ∧ ‖z.2‖=1 := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := canonicalSphereMeasureND V)
    (ν := canonicalSphereMeasureND V)).tendsto_ae.eventually canonicalSphereMeasureND_ae_norm,
    (Measure.quasiMeasurePreserving_snd (μ := canonicalSphereMeasureND V)
    (ν := canonicalSphereMeasureND V)).tendsto_ae.eventually canonicalSphereMeasureND_ae_norm]
    with z h₁ h₂
  exact ⟨h₁,h₂⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_norm [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (Λ : ℝ) (e w : V) : ‖spherePlaneWaveND Λ e w‖ = 1 := by
  simp [spherePlaneWaveND,Complex.norm_exp,Complex.mul_re]

lemma graphFixedSpatialTermND_radial (Ψ : ℝ → ℂ) (Q : ℝ) (e₁ e₂ : V)
    (b₁ b₂ : V → ℂ) (hΨ : Continuous Ψ) (hiΨ : Integrable Ψ)
    (hb₁ : Continuous b₁) (hb₂ : Continuous b₂) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁)
    (_hB₂ : 0 ≤ B₂) (hbd₁ : ∀ w, ‖w‖=1 → ‖b₁ w‖ ≤ B₁)
    (hbd₂ : ∀ w, ‖w‖=1 → ‖b₂ w‖ ≤ B₂) :
    graphFixedSpatialTermND Ψ Q e₁ e₂ b₁ b₂ =
      ∫ z : V×V, radialPhaseIntegral Ψ (Q*(inner ℝ z.1 e₁+inner ℝ z.2 e₂))*b₁ z.1*b₂ z.2
        ∂(canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V) := by
  let μ := canonicalSphereMeasureND V
  let F (u : ℝ) (z : V×V) := Ψ u*
    ((spherePlaneWaveND (Q*u) e₁ z.1*b₁ z.1)*(spherePlaneWaveND (Q*u) e₂ z.2*b₂ z.2))
  have hFc : Continuous (Function.uncurry F) := by
    dsimp [F,spherePlaneWaveND,Function.uncurry]
    fun_prop
  have hmajor := (hiΨ.norm.comp_fst (μ.prod μ)).mul_const (B₁*B₂)
  have hFi : Integrable (Function.uncurry F) (volume.prod (μ.prod μ)) := by
    apply hmajor.mono' hFc.aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volume) (ν := μ.prod μ)).tendsto_ae.eventually
      canonicalSphereMeasureND_prod_ae_norm] with p hp
    simp only [F,Function.uncurry,norm_mul,spherePlaneWaveND_norm,one_mul]
    gcongr
    · exact hbd₁ p.2.1 hp.1
    · exact hbd₂ p.2.2 hp.2
  calc
    _ = ∫ u : ℝ, ∫ z : V×V, F u z ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [show (∫ z, F u z ∂μ.prod μ) = Ψ u*
        ((∫ w, spherePlaneWaveND (Q*u) e₁ w*b₁ w ∂μ)*
         (∫ w, spherePlaneWaveND (Q*u) e₂ w*b₂ w ∂μ)) by
          dsimp [F]
          rw [integral_const_mul,integral_prod_mul
            (fun w => spherePlaneWaveND (Q*u) e₁ w*b₁ w)
            (fun w => spherePlaneWaveND (Q*u) e₂ w*b₂ w)]]
      exact mul_assoc _ _ _
    _ = ∫ z : V×V, ∫ u : ℝ, F u z ∂volume ∂μ.prod μ := integral_integral_swap hFi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold radialPhaseIntegral
      rw [← integral_mul_const,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with u
      have hex : spherePlaneWaveND (Q*u) e₁ z.1*spherePlaneWaveND (Q*u) e₂ z.2 =
          Complex.exp (Complex.I*(Q*(inner ℝ z.1 e₁+inner ℝ z.2 e₂):ℝ)*(u:ℂ)) := by
        rw [spherePlaneWaveND,spherePlaneWaveND,← Complex.exp_add]
        congr 1
        push_cast
        ring
      dsimp [F]
      calc
        _ = (spherePlaneWaveND (Q*u) e₁ z.1*spherePlaneWaveND (Q*u) e₂ z.2)*Ψ u*b₁ z.1*b₂ z.2 := by ring
        _ = _ := by rw [hex]

lemma graphFixedSpatialTermND_swap (Ψ : ℝ → ℂ) (Q : ℝ) (e₁ e₂ : V) (b₁ b₂ : V → ℂ) :
    graphFixedSpatialTermND Ψ Q e₁ e₂ b₁ b₂ = graphFixedSpatialTermND Ψ Q e₂ e₁ b₂ b₁ := by
  unfold graphFixedSpatialTermND
  apply integral_congr_ae
  filter_upwards [] with u
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma graph_center_scalar_error [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (w₀ w d e : V) (hw : ‖w₀‖=1) :
    |inner ℝ w e-inner ℝ w₀ d| ≤ ‖w-w₀‖*‖e‖+‖e-d‖ := by
  have he : inner ℝ w e-inner ℝ w₀ d = inner ℝ (w-w₀) e+inner ℝ w₀ (e-d) := by
    simp only [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  exact add_le_add (abs_real_inner_le_norm _ _) (by simpa [hw] using abs_real_inner_le_norm w₀ (e-d))

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma graphFixedSpatialTermND_angular_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → ℂ) (w₀ d e e' : V)
      (Q τ δ D η A K B B' : ℝ) (b b' : V → ℂ),
      Continuous Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 → (∫ u : ℝ, ‖Ψ u‖) ≤ K →
      ‖w₀‖=1 → 0 < Q → 0 < τ → 0 ≤ δ → 0 ≤ D → 0 ≤ η → 1 ≤ A →
      0 ≤ K → 0 ≤ B → 0 ≤ B' →
      ‖e‖ ≤ D → ‖e-d‖ ≤ η → 2*δ*D+η ≤ τ/2 →
      τ < ‖d-inner ℝ d w₀ • w₀‖ → ContDiff ℝ ∞ b →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      (∀ w, ‖w‖=1 → b w ≠ 0 → ‖w-w₀‖ ≤ δ) →
      (∀ w, ‖w‖=1 → ‖b' w‖ ≤ B') →
      ‖graphFixedSpatialTermND Ψ Q e e' b b'‖ ≤
        C*K*B*B'*((A+1+D/τ)/(Q*τ))^m := by
  obtain ⟨C,hC,hCb⟩ := sphere_cap_nonstationary_uniform (V := V) m
  let S := (canonicalSphereMeasureND V).real univ
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  refine ⟨C*4^m*S,by positivity,?_⟩
  intro Ψ w₀ d e e' Q τ δ D η A K B B' b b' hΨ hsΨ hK hw hQ hτ hδ hD hη hA hK0 hB hB'
    he hed herr hfail hb hbd hs hb'
  let r := (A+1+D/τ)/(Q*τ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hΨi : Integrable Ψ := hΨ.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure hsΨ)
  have hbound : ∀ u : ℝ, ‖Ψ u*sphereAxisIntegralND (Q*u) e b*sphereAxisIntegralND (Q*u) e' b'‖ ≤
      ‖Ψ u‖*((C*4^m*S)*B*B'*r^m) := by
    intro u
    by_cases hzero : Ψ u=0
    · simp [hzero]
    have hu := hsΨ (subset_closure hzero)
    have hup : 0 < u := by linarith [hu.1]
    have hh := hCb w₀ d e (Q*u) τ δ D η A B b hw (mul_pos hQ hup) hτ hδ hD hη hA hB
      he hed herr hfail hb hbd hs
    have hr' : (A+1+D/τ)/((Q*u)*τ) ≤ 4*r := by
      rw [show (A+1+D/τ)/((Q*u)*τ)=r/u by dsimp [r]; ring]
      apply (div_le_iff₀ hup).2
      nlinarith [hu.1]
    have hhn : ‖sphereAxisIntegralND (Q*u) e b‖ ≤ C*B*(4*r)^m :=
      hh.trans (by gcongr)
    have hbn : ‖sphereAxisIntegralND (Q*u) e' b'‖ ≤ S*B' := sphereAxisIntegralND_norm_le hb'
    calc
      _ = ‖Ψ u‖*‖sphereAxisIntegralND (Q*u) e b‖*‖sphereAxisIntegralND (Q*u) e' b'‖ := by simp only [norm_mul]
      _ ≤ ‖Ψ u‖*(C*B*(4*r)^m)*(S*B') := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hh := norm_integral_le_of_norm_le (hΨi.norm.mul_const ((C*4^m*S)*B*B'*r^m))
    (Filter.Eventually.of_forall hbound)
  rw [integral_mul_const] at hh
  apply hh.trans
  change (∫ u : ℝ, ‖Ψ u‖)*((C*4^m*S)*B*B'*r^m) ≤ _
  calc
    _ ≤ K*((C*4^m*S)*B*B'*r^m) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by ring

lemma graphFixedSpatialTermND_radial_bound (m : ℕ)
    (Ψ : ℝ → ℂ) (w₁ w₂ d₁ d₂ e₁ e₂ : V) (Q τ δ D η K B₁ B₂ : ℝ)
    (b₁ b₂ : V → ℂ)
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : tsupport Ψ ⊆ Icc (1/4:ℝ) 4)
    (hdΨ : ∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K)
    (hw₁ : ‖w₁‖=1) (hw₂ : ‖w₂‖=1) (hQ : 0 < Q) (hτ : 0 < τ)
    (hδ : 0 ≤ δ) (_hD : 0 ≤ D) (_hη : 0 ≤ η) (hK : 0 ≤ K) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (he₁ : ‖e₁‖ ≤ D) (he₂ : ‖e₂‖ ≤ D) (hed₁ : ‖e₁-d₁‖ ≤ η) (hed₂ : ‖e₂-d₂‖ ≤ η)
    (herr : 2*δ*D+2*η ≤ τ/2) (hfail : τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂|)
    (hb₁ : Continuous b₁) (hb₂ : Continuous b₂)
    (hbd₁ : ∀ w, ‖w‖=1 → ‖b₁ w‖ ≤ B₁) (hbd₂ : ∀ w, ‖w‖=1 → ‖b₂ w‖ ≤ B₂)
    (hs₁ : ∀ w, ‖w‖=1 → b₁ w ≠ 0 → ‖w-w₁‖ ≤ δ)
    (hs₂ : ∀ w, ‖w‖=1 → b₂ w ≠ 0 → ‖w-w₂‖ ≤ δ) :
    ‖graphFixedSpatialTermND Ψ Q e₁ e₂ b₁ b₂‖ ≤
      (4*2^m*((canonicalSphereMeasureND V).real univ)^2)*K*B₁*B₂*(1/(Q*τ))^m := by
  have hΨi : Integrable Ψ := hΨ.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure hsΨ)
  rw [graphFixedSpatialTermND_radial Ψ Q e₁ e₂ b₁ b₂ hΨ.continuous hΨi hb₁ hb₂ hB₁ hB₂ hbd₁ hbd₂]
  have hpoint : ∀ᵐ z : V×V ∂(canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V),
      ‖radialPhaseIntegral Ψ (Q*(inner ℝ z.1 e₁+inner ℝ z.2 e₂))*b₁ z.1*b₂ z.2‖ ≤
        (4*2^m)*K*B₁*B₂*(1/(Q*τ))^m := by
    filter_upwards [canonicalSphereMeasureND_prod_ae_norm] with z hz
    by_cases hzero₁ : b₁ z.1=0
    · simp only [hzero₁,mul_zero,zero_mul,norm_zero]; positivity
    by_cases hzero₂ : b₂ z.2=0
    · simp only [hzero₂,mul_zero,norm_zero]; positivity
    have hgeom₁ : |inner ℝ z.1 e₁-inner ℝ w₁ d₁| ≤ δ*D+η := by
      apply (graph_center_scalar_error w₁ z.1 d₁ e₁ hw₁).trans
      gcongr
      exact hs₁ z.1 hz.1 hzero₁
    have hgeom₂ : |inner ℝ z.2 e₂-inner ℝ w₂ d₂| ≤ δ*D+η := by
      apply (graph_center_scalar_error w₂ z.2 d₂ e₂ hw₂).trans
      gcongr
      exact hs₂ z.2 hz.2 hzero₂
    let s := inner ℝ z.1 e₁+inner ℝ z.2 e₂
    let s₀ := inner ℝ w₁ d₁+inner ℝ w₂ d₂
    have hdiff : |s-s₀| ≤ 2*δ*D+2*η := by
      have hre : s-s₀=(inner ℝ z.1 e₁-inner ℝ w₁ d₁)+(inner ℝ z.2 e₂-inner ℝ w₂ d₂) := by dsimp [s,s₀]; ring
      rw [hre]
      apply (abs_add_le _ _).trans
      linarith
    have hsf : τ/2 < |s| := by
      have hh := abs_sub_abs_le_abs_sub s₀ s
      rw [abs_sub_comm] at hh
      change τ < |s₀| at hfail
      linarith
    have hfreq : Q*τ/2 ≤ |Q*s| := by rw [abs_mul,abs_of_pos hQ]; nlinarith
    have hfp : 0 < |Q*s| := lt_of_lt_of_le (by positivity) hfreq
    have hrad := radialPhaseIntegral_nonzero hΨ hsΨ (by norm_num) (abs_pos.mp hfp) m hdΨ
    have hbq : ‖radialPhaseIntegral Ψ (Q*s)‖ ≤ (4*2^m)*K*(1/(Q*τ))^m := by
      calc
        _ ≤ K*((4:ℝ)-1/4)/|Q*s|^m := hrad
        _ ≤ K*4/(Q*τ/2)^m := by
          apply div_le_div₀ (by positivity) _ (by positivity) _
          · nlinarith
          · exact pow_le_pow_left₀ (by positivity) hfreq m
        _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,inv_inv,mul_pow]; ring
    change ‖radialPhaseIntegral Ψ (Q*s)*b₁ z.1*b₂ z.2‖ ≤ _
    calc
      _ = ‖radialPhaseIntegral Ψ (Q*s)‖*‖b₁ z.1‖*‖b₂ z.2‖ := by simp only [norm_mul]
      _ ≤ ((4*2^m)*K*(1/(Q*τ))^m)*B₁*B₂ := by gcongr; exact hbd₁ z.1 hz.1; exact hbd₂ z.2 hz.2
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le_const hpoint
  apply hh.trans_eq
  have hmass : ((canonicalSphereMeasureND V).prod (canonicalSphereMeasureND V)).real univ =
      ((canonicalSphereMeasureND V).real univ)^2 := by
    rw [Measure.real,← univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
    simp only [Measure.real,pow_two]
  rw [hmass]
  ring

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace

theorem graph_fixed_nonedge_term_uniform
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ψ : ℝ → ℂ) (w₁ w₂ d₁ d₂ e₁ e₂ : V) (Q τ δ D η A K B₁ B₂ : ℝ)
        (b₁ b₂ : V → ℂ),
      ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
      (∫ u : ℝ, ‖Ψ u‖) ≤ K → (∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K) →
      ‖w₁‖=1 → ‖w₂‖=1 → 0 < Q → 0 < τ → 0 ≤ δ → 0 ≤ D → 0 ≤ η →
      1 ≤ A → 0 ≤ K → 0 ≤ B₁ → 0 ≤ B₂ →
      ‖e₁‖ ≤ D → ‖e₂‖ ≤ D → ‖e₁-d₁‖ ≤ η → ‖e₂-d₂‖ ≤ η →
      4*δ*D+2*η ≤ τ/2 →
      ¬(‖d₁-inner ℝ d₁ w₁ • w₁‖ ≤ τ ∧
        ‖d₂-inner ℝ d₂ w₂ • w₂‖ ≤ τ ∧
        |inner ℝ w₁ d₁+inner ℝ w₂ d₂| ≤ τ) →
      ContDiff ℝ ∞ b₁ → ContDiff ℝ ∞ b₂ →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b₁ w‖ ≤ B₁*A^j) →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b₂ w‖ ≤ B₂*A^j) →
      (∀ w, ‖w‖=1 → b₁ w ≠ 0 → ‖w-w₁‖ ≤ δ) →
      (∀ w, ‖w‖=1 → b₂ w ≠ 0 → ‖w-w₂‖ ≤ δ) →
      ‖graphFixedSpatialTermND Ψ Q e₁ e₂ b₁ b₂‖ ≤
        C*K*B₁*B₂*((A+1+D/τ)/(Q*τ))^m := by
  obtain ⟨Ca,hCa,hCab⟩ := graphFixedSpatialTermND_angular_bound (V := V) m
  let Cr := 4*2^m*((canonicalSphereMeasureND V).real univ)^2
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  refine ⟨Ca+Cr,add_nonneg hCa hCr,?_⟩
  intro Ψ w₁ w₂ d₁ d₂ e₁ e₂ Q τ δ D η A K B₁ B₂ b₁ b₂
    hΨ hsΨ hK hdΨ hw₁ hw₂ hQ hτ hδ hD hη hA hK0 hB₁ hB₂
    he₁ he₂ hed₁ hed₂ herr hne hb₁ hb₂ hd₁ hd₂ hs₁ hs₂
  have hbd₁ : ∀ w, ‖w‖=1 → ‖b₁ w‖ ≤ B₁ := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hd₁ 0 (Nat.zero_le _) w hw
  have hbd₂ : ∀ w, ‖w‖=1 → ‖b₂ w‖ ≤ B₂ := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hd₂ 0 (Nat.zero_le _) w hw
  have herrA : 2*δ*D+η ≤ τ/2 := by nlinarith [mul_nonneg hδ hD]
  have herrR : 2*δ*D+2*η ≤ τ/2 := by nlinarith [mul_nonneg hδ hD]
  have hratio0 : 0 ≤ (A+1+D/τ)/(Q*τ) := by positivity
  by_cases hfirst : τ < ‖d₁-inner ℝ d₁ w₁ • w₁‖
  · have hh := hCab Ψ w₁ d₁ e₁ e₂ Q τ δ D η A K B₁ B₂ b₁ b₂ hΨ.continuous
      hsΨ hK hw₁ hQ hτ hδ hD hη hA hK0 hB₁ hB₂ he₁ hed₁ herrA hfirst hb₁ hd₁ hs₁ hbd₂
    apply hh.trans
    gcongr; linarith
  by_cases hsecond : τ < ‖d₂-inner ℝ d₂ w₂ • w₂‖
  · have hh := hCab Ψ w₂ d₂ e₂ e₁ Q τ δ D η A K B₂ B₁ b₂ b₁ hΨ.continuous
      hsΨ hK hw₂ hQ hτ hδ hD hη hA hK0 hB₂ hB₁ he₂ hed₂ herrA hsecond hb₂ hd₂ hs₂ hbd₁
    rw [graphFixedSpatialTermND_swap Ψ Q e₁ e₂ b₁ b₂]
    have hc : Ca*K*B₂*B₁=Ca*K*B₁*B₂ := by ring
    rw [hc] at hh
    apply hh.trans
    gcongr; linarith
  have hlast : τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂| := by
    apply lt_of_not_ge
    intro hl
    exact hne ⟨le_of_not_gt hfirst,le_of_not_gt hsecond,hl⟩
  have hh := graphFixedSpatialTermND_radial_bound m Ψ w₁ w₂ d₁ d₂ e₁ e₂ Q τ δ D η K B₁ B₂ b₁ b₂
    hΨ hsΨ hdΨ hw₁ hw₂ hQ hτ hδ hD hη hK0 hB₁ hB₂ he₁ he₂ hed₁ hed₂ herrR hlast
    hb₁.continuous hb₂.continuous hbd₁ hbd₂ hs₁ hs₂
  change ‖graphFixedSpatialTermND Ψ Q e₁ e₂ b₁ b₂‖ ≤ Cr*K*B₁*B₂*(1/(Q*τ))^m at hh
  have hratio : 1/(Q*τ) ≤ (A+1+D/τ)/(Q*τ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ D/τ := div_nonneg hD hτ.le
    linarith
  apply hh.trans
  gcongr; linarith

end Attempt4FullFar
end
end

end OAI
