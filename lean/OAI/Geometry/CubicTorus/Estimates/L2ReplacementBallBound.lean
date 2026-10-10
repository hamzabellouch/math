import Mathlib
import OAI.Geometry.CubicTorus.Estimates.PlaneScaleEquiv

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_replacement_ball_bound (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) (q : Plane) {ρ M : ℝ} (hρ : 0≤ρ) (hM : 0≤M)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 ρ)] H)
    (hb : ∀ y∈Metric.ball 0 ρ,‖H y-q‖≤M) :
    (∫ y in Metric.ball 0 ρ,‖G y-q‖^2)≤2*‖W‖^2+2*Real.pi*ρ^2*M^2 := by
  have hi := plane_L2_sub_const_integrable G q ρ
  have hw := (L2_vector_norm_sq_integrable W).integrableOn (s := Metric.ball 0 ρ)
  have hc : IntegrableOn (fun _ : Plane ↦ 2*M^2) (Metric.ball 0 ρ) :=
    integrableOn_const measure_ball_lt_top.ne
  have hpoint : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) ρ),
      ‖G y-q‖^2≤2*‖W y‖^2+2*M^2 := by
    filter_upwards [he,ae_restrict_of_ae (Lp.coeFn_sub G W),ae_restrict_mem measurableSet_ball]
      with y hy hz hys
    change (G-W : Lp Plane 2 volume) y=H y at hy
    change (G-W : Lp Plane 2 volume) y=G y-W y at hz
    have hEq : G y-q=W y+(H y-q) := by rw [← hy,hz]; abel
    have hn := (norm_add_le (W y) (H y-q))
    rw [← hEq] at hn
    have hs := (sq_le_sq₀ (norm_nonneg (H y-q)) hM).mpr (hb y hys)
    nlinarith [sq_nonneg (‖W y‖-‖H y-q‖),norm_nonneg (G y-q),norm_nonneg (W y),norm_nonneg (H y-q)]
  calc
    _ ≤ ∫ y in Metric.ball 0 ρ,2*‖W y‖^2+2*M^2 :=
      integral_mono_ae hi ((hw.const_mul 2).add hc) hpoint
    _ = 2*(∫ y in Metric.ball 0 ρ,‖W y‖^2)+2*Real.pi*ρ^2*M^2 := by
      rw [integral_add (hw.const_mul 2) hc,integral_const_mul,integral_const,smul_eq_mul]
      rw [show (volume.restrict (Metric.ball (0 : Plane) ρ)).real univ=
        volume.real (Metric.ball (0 : Plane) ρ) by simp [Measure.real],plane_ball_real hρ]
      ring
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [L2_vector_norm_sq_integral]
      exact setIntegral_le_integral (L2_vector_norm_sq_integrable W)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)

lemma L2_replacement_energy_decay (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) {R ρ M : ℝ} (hρ : 0≤ρ) (hρR : ρ≤R) (hM : 0≤M)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H)
    (hb : ∀ y,‖H y‖≤M) :
    (∫ y in Metric.ball 0 ρ,‖G y‖^2)≤2*‖W‖^2+2*Real.pi*ρ^2*M^2 := by
  simpa only [sub_zero] using L2_replacement_ball_bound G W H 0 hρ hM
    (ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρR)) he)
    (fun y _ ↦ by simpa only [sub_zero] using hb y)

lemma L2_replacement_oscillation_decay (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) {R ρ L : ℝ} (hρ : 0≤ρ) (hρR : ρ≤R) (hL : 0≤L)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H)
    (hl : ∀ x y,‖H x-H y‖≤L*‖x-y‖) :
    (∫ y in Metric.ball 0 ρ,‖G y-H 0‖^2)≤2*‖W‖^2+2*Real.pi*L^2*ρ^4 := by
  have hb : ∀ y∈Metric.ball 0 ρ,‖H y-H 0‖≤L*ρ := by
    intro y hy
    have hn : ‖y‖≤ρ := (show ‖y‖<ρ from by
      simpa only [Metric.mem_ball,dist_zero_right] using hy).le
    have hh : ‖H y-H 0‖≤L*‖y‖ := by simpa only [sub_zero] using hl y 0
    exact hh.trans (mul_le_mul_of_nonneg_left hn hL)
  have hh := L2_replacement_ball_bound G W H (H 0) hρ (mul_nonneg hL hρ)
    (ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρR)) he) hb
  convert hh using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weak_divergence_local_congr {S : Set Plane} (hS : MeasurableSet S)
    {G G' : Plane → Plane} (A : Plane → Plane →L[ℝ] Plane)
    (hG : G'=ᵐ[volume.restrict S] G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G y)))=0) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G' y)))=0 := by
  have he := (ae_restrict_iff' hS).mp hG
  intro ψ hψ hc hs
  rw [← hd ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with y hy
  by_cases hys : y∈S
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,zero_apply]

lemma L2_gradient_truncate (G : Lp Plane 2 (volume : Measure Plane))
    {S : Set Plane} (hS : MeasurableSet S) :
    ∃ G' : Lp Plane 2 (volume : Measure Plane),
      (G' : Plane → Plane)=ᵐ[volume.restrict S] G ∧
      (∀ᵐ y ∂volume,y∉S → G' y=0) ∧
      ‖G'‖^2=(∫ y in S,‖G y‖^2) := by
  have hm := (Lp.memLp G).indicator hS
  let G' := hm.toLp (S.indicator (G : Plane → Plane))
  refine ⟨G',?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hm.coeFn_toLp,ae_restrict_mem hS] with y hy hys
    exact hy.trans (indicator_of_mem hys _)
  · filter_upwards [hm.coeFn_toLp] with y hy hys
    exact hy.trans (indicator_of_notMem hys _)
  · rw [L2_vector_norm_sq_integral,← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with y hy
    change ‖G' y‖^2=S.indicator (fun y ↦ ‖G y‖^2) y
    change G' y=S.indicator (G : Plane → Plane) y at hy
    rw [hy]
    by_cases hys : y∈S <;> simp [hys]

lemma plane_L2_energy_mono (G : Lp Plane 2 (volume : Measure Plane)) :
    Monotone (fun r : ℝ ↦ ∫ y in Metric.ball (0 : Plane) r,‖G y‖^2) := by
  intro r s hrs
  exact setIntegral_mono_set (L2_vector_norm_sq_integrable G).integrableOn
    (Eventually.of_forall fun _ ↦ sq_nonneg _) (Metric.ball_subset_ball hrs).eventuallyLE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma forced_replacement_energy_algebra {w g b δ K : ℝ}
    (hw : 0≤w) (_hg : 0≤g) (_hb : 0≤b) (_hδ : 0≤δ) (hK : 0≤K)
    (hwg : w≤8*δ*g+8*b) :
    2*w^2+K*(g+b)^2≤(2*K+256*δ^2)*g^2+(2*K+256)*b^2 := by
  have hsq := pow_le_pow_left₀ hw hwg 2
  have hs : (g+b)^2≤2*g^2+2*b^2 := by nlinarith [sq_nonneg (g-b)]
  have hmul := mul_le_mul_of_nonneg_left hs hK
  nlinarith [sq_nonneg (δ*g-b)]

theorem forced_cmc_replacement_decay :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane))
      (G B : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball 0 ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+256*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2)+(A+256)*‖B‖^2 ∧
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+256*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2)+(A+256)*‖B‖^2 := by
  obtain ⟨C,hC,hbound⟩ := forced_cmc_replacement_bounds
  let A := 4*Real.pi*C^2
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A,hA,fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G B hg hd ↦ ?_⟩
  obtain ⟨G',he,hgs,hn⟩ := L2_gradient_truncate G
    (S := Metric.ball (0 : Plane) (8*R)) measurableSet_ball
  have hg' := PlaneWeakGradient.local_congr measurableSet_ball hg EventuallyEq.rfl he
  have hde : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G' y)-B y))=0 := by
    intro ψ hψ hc hs
    rw [← hd ψ hψ hc hs]
    apply integral_congr_ae
    have he' := (ae_restrict_iff' measurableSet_ball).mp he
    filter_upwards [he'] with y hy
    by_cases hy' : y∈Metric.ball (0 : Plane) (8*R)
    · rw [hy hy']
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hy' (hs hh))]; rfl
  obtain ⟨w,W,H,hW,hw,herr,hH,hrep,hb,hl⟩ :=
    hbound p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G' B hgs hg' hde
  refine ⟨H 0,fun ρ hρ hρR ↦ ?_⟩
  have hρ8 : ρ≤8*R := by linarith
  have heρ := ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρ8)) he
  have heq (q : Plane) : (∫ y in Metric.ball 0 ρ,‖G' y-q‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2) := by
    apply integral_congr_ae
    filter_upwards [heρ] with y hy
    rw [hy]
  have heq0 : (∫ y in Metric.ball 0 ρ,‖G' y‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y‖^2) := by simpa only [sub_zero] using heq 0
  have hh := L2_replacement_energy_decay G' W H hρ hρR
    (by positivity : 0≤C*R⁻¹*(‖G'‖+‖B‖)) hrep hb
  have ho := L2_replacement_oscillation_decay G' W H hρ hρR
    (by positivity : 0≤C*R⁻¹^2*(‖G'‖+‖B‖)) hrep hl
  rw [heq0] at hh
  rw [heq (H 0)] at ho
  have hr : 0≤ρ/R := div_nonneg hρ hR.le
  have hr1 : ρ/R≤1 := (div_le_one hR).mpr (by linarith)
  have hc2 : A*(ρ/R)^2≤A := mul_le_of_le_one_right hA.le (pow_le_one₀ hr hr1)
  have hc4 : A*(ρ/R)^4≤A := mul_le_of_le_one_right hA.le (pow_le_one₀ hr hr1)
  constructor
  · calc
      _ ≤ 2*‖W‖^2+(2*Real.pi*ρ^2*(C*R⁻¹)^2)*(‖G'‖+‖B‖)^2 := by convert hh using 1; ring
      _ ≤ (2*(2*Real.pi*ρ^2*(C*R⁻¹)^2)+256*δ^2)*‖G'‖^2+
          (2*(2*Real.pi*ρ^2*(C*R⁻¹)^2)+256)*‖B‖^2 :=
        forced_replacement_energy_algebra (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hδ (by positivity) herr
      _ = (A*(ρ/R)^2+256*δ^2)*‖G'‖^2+(A*(ρ/R)^2+256)*‖B‖^2 := by dsimp [A]; ring
      _ ≤ (A*(ρ/R)^2+256*δ^2)*‖G'‖^2+(A+256)*‖B‖^2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add hc2 le_rfl) (sq_nonneg _))
      _ = _ := by rw [hn]
  · calc
      _ ≤ 2*‖W‖^2+(2*Real.pi*(C*R⁻¹^2)^2*ρ^4)*(‖G'‖+‖B‖)^2 := by convert ho using 1; ring
      _ ≤ (2*(2*Real.pi*(C*R⁻¹^2)^2*ρ^4)+256*δ^2)*‖G'‖^2+
          (2*(2*Real.pi*(C*R⁻¹^2)^2*ρ^4)+256)*‖B‖^2 :=
        forced_replacement_energy_algebra (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hδ (by positivity) herr
      _ = (A*(ρ/R)^4+256*δ^2)*‖G'‖^2+(A*(ρ/R)^4+256)*‖B‖^2 := by dsimp [A]; ring
      _ ≤ (A*(ρ/R)^4+256*δ^2)*‖G'‖^2+(A+256)*‖B‖^2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add hc4 le_rfl) (sq_nonneg _))
      _ = _ := by rw [hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma memLp_gradient_test_integrable {F : Plane → Plane} (hF : MemLp F 2 volume)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y ↦ fderiv ℝ ψ y (F y)) := by
  have hm := compact_C1_gradient_memLp hψ hc
  apply (L2.integrable_inner (𝕜 := ℝ) (hF.toLp F) (hm.toLp (gradient ψ))).congr
  filter_upwards [hF.coeFn_toLp,hm.coeFn_toLp] with y hy hz
  simp only [hy,hz,inner_gradient_right,conj_trivial]

lemma local_divergence_source {B : Plane → Plane} (hB : Continuous B)
    (B₀ : Plane) {R η : ℝ} (hR : 0<R) (_hη : 0≤η)
    (hbound : ∀ y∈Metric.ball (0 : Plane) R,‖B y-B₀‖≤η) :
    ∃ B' : Lp Plane 2 (volume : Measure Plane),
      (B' : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] (fun y ↦ B y-B₀) ∧
      ‖B'‖^2≤Real.pi*R^2*η^2 := by
  let S := Metric.ball (0 : Plane) R
  have hme : AEStronglyMeasurable (S.indicator (fun y ↦ B y-B₀)) volume :=
    (hB.sub continuous_const).aestronglyMeasurable.indicator measurableSet_ball
  have hm : MemLp (S.indicator (fun y ↦ B y-B₀)) 2 volume := by
    apply (memLp_indicator_const (s := S) 2 measurableSet_ball η (Or.inr measure_ball_lt_top.ne)).mono' hme
    exact Eventually.of_forall fun y ↦ by
      by_cases hy : y∈S
      · simp only [indicator_of_mem hy]
        exact hbound y hy
      · simp only [indicator_of_notMem hy,norm_zero,le_refl]
  let B' := hm.toLp (S.indicator (fun y ↦ B y-B₀))
  have he : (B' : Plane → Plane)=ᵐ[volume.restrict S] (fun y ↦ B y-B₀) := by
    filter_upwards [ae_restrict_of_ae hm.coeFn_toLp,ae_restrict_mem measurableSet_ball] with y hy hz
    exact hy.trans (indicator_of_mem hz _)
  refine ⟨B',he,?_⟩
  have hnorm : ‖B'‖^2=(∫ y in S,‖B y-B₀‖^2) := by
    rw [L2_vector_norm_sq_integral,← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with y hy
    change ‖B' y‖^2=S.indicator (fun y ↦ ‖B y-B₀‖^2) y
    change B' y=S.indicator (fun y ↦ B y-B₀) y at hy
    rw [hy]
    by_cases hz : y∈S <;> simp [hz]
  rw [hnorm]
  have hi : IntegrableOn (fun y ↦ ‖B y-B₀‖^2) S :=
    (((hB.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) R)).mono_set Metric.ball_subset_closedBall
  calc
    _ ≤ ∫ y in S,η^2 := by
      apply integral_mono_ae hi (integrableOn_const measure_ball_lt_top.ne)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound y hy) 2
    _ = _ := by simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
                rw [show (volume S).toReal=Real.pi*R^2 from plane_ball_real hR.le]

lemma forced_divergence_localize {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) (G : Lp Plane 2 (volume : Measure Plane))
    {B : Plane → Plane} (hB : Continuous B) {S : Set Plane} (hS : MeasurableSet S)
    (B₀ : Plane) (B' : Lp Plane 2 (volume : Measure Plane))
    (he : (B' : Plane → Plane)=ᵐ[volume.restrict S] (fun y ↦ B y-B₀))
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B' y))=0 := by
  intro ψ hψ hc hs
  have hm := bounded_coefficient_memLp
    (cmcJacobian_contDiff.continuous.comp hp).aestronglyMeasurable
    (Eventually.of_forall fun y v ↦ cmcJacobian_norm_le (hpb y) v) G
  have hiA := memLp_gradient_test_integrable hm (hψ.of_le (by simp)) hc
  have hdψ := hψ.continuous_fderiv (by simp)
  have hiB : Integrable (fun y ↦ fderiv ℝ ψ y (B y)) :=
    (hdψ.clm_apply hB).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).mono (by
        intro y hy
        contrapose! hy
        simp only [Function.mem_support,not_not] at hy ⊢
        rw [hy]; simp))
  have hi₀ : Integrable (fun y ↦ fderiv ℝ ψ y B₀) :=
    (hdψ.clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ B₀)
  have he' := (ae_restrict_iff' hS).mp he
  calc
    _ = ∫ y,(fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))+fderiv ℝ ψ y B₀ := by
      apply integral_congr_ae
      filter_upwards [he'] with y hy
      by_cases hz : y∈S
      · rw [hy hz,sub_sub_eq_add_sub,add_sub_right_comm,map_add]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hz (hs hh))]; simp
    _ = (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))+(∫ y,fderiv ℝ ψ y B₀) := by
      apply integral_add _ hi₀
      apply (hiA.sub hiB).congr
      exact Eventually.of_forall fun y ↦ by simp only [Pi.sub_apply,Function.comp_apply,map_sub]
    _ = 0 := by rw [hd ψ hψ hc hs,integral_compact_fderiv_zero hψ hc B₀,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.comp_add {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (hg : PlaneWeakGradient S u G) (a : Plane) :
    PlaneWeakGradient ((fun y ↦ y+a) ⁻¹' S) (fun y ↦ u (y+a)) (fun y ↦ G (y+a)) := by
  intro v ψ hψ hc hs
  let φ : Plane → ℝ := fun y ↦ ψ (y + -a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight (-a))
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ Homeomorph.addRight (-a))⊆S
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simpa using hh
  have hh := hg v φ hφ hφc hφs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ ⟪G y,v⟫*φ y) a
  have hj := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ u y*fderiv ℝ φ y v) a
  simp only [φ,fderiv_comp_add_right,add_neg_cancel_right] at hi hj hh
  rw [hi,hj]
  exact hh

lemma variable_divergence_comp_add {S : Set Plane} (A : Plane → Plane →L[ℝ] Plane)
    (G : Plane → Plane)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G y)))=0) (a : Plane) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆(fun y ↦ y+a) ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (A (y+a) (G (y+a))))=0 := by
  intro ψ hψ hc hs
  let φ : Plane → ℝ := fun y ↦ ψ (y + -a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight (-a))
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ Homeomorph.addRight (-a))⊆S
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simpa using hh
  have hh := hd φ hφ hφc hφs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ φ y (A y (G y))) a
  simp only [φ,fderiv_comp_add_right,add_neg_cancel_right] at hh hi
  exact hi.trans hh

lemma translate_preimage_ball (a : Plane) (r : ℝ) :
    (fun y : Plane ↦ y+a) ⁻¹' Metric.ball a r=Metric.ball 0 r := by
  ext y
  simp [dist_eq_norm]

lemma translate_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : Plane) (r : ℝ) (f : Plane → X) :
    (∫ y in Metric.ball 0 r,f (y+a))=(∫ y in Metric.ball a r,f y) := by
  have hh := ((measurePreserving_add_right (volume : Measure Plane) a).restrict_preimage
    (s := Metric.ball a r) measurableSet_ball).integral_comp
      (Homeomorph.addRight a).measurableEmbedding f
  rwa [translate_preimage_ball] at hh

lemma L2_translate (G : Lp Plane 2 (volume : Measure Plane)) (a : Plane) :
    ∃ G' : Lp Plane 2 (volume : Measure Plane),
      (G' : Plane → Plane)=ᵐ[volume] (fun y ↦ G (y+a)) ∧
      ‖G'‖^2=‖G‖^2 ∧
      ∀ r : ℝ,∀ q : Plane,(∫ y in Metric.ball 0 r,‖G' y-q‖^2)=
        (∫ y in Metric.ball a r,‖G y-q‖^2) := by
  have hm := (Lp.memLp G).comp_measurePreserving (measurePreserving_add_right volume a)
  let G' := hm.toLp ((G : Plane → Plane) ∘ (fun y ↦ y+a))
  have he : (G' : Plane → Plane)=ᵐ[volume] (fun y ↦ G (y+a)) := hm.coeFn_toLp
  refine ⟨G',he,?_,fun r q ↦ ?_⟩
  · rw [L2_vector_norm_sq_integral,L2_vector_norm_sq_integral]
    exact (integral_congr_ae (he.fun_comp (fun z ↦ ‖z‖^2))).trans
      (integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ ‖G y‖^2) a)
  · calc
      _ = ∫ y in Metric.ball 0 r,‖G (y+a)-q‖^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae he] with y hy
        rw [hy]
      _ = _ := translate_setIntegral a r (fun y ↦ ‖G y-q‖^2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem forced_cmc_replacement_decay_at :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ (a : Plane) (R δ η : ℝ),0<R → 0≤δ → δ≤1 → 0≤η →
    (∀ y∈Metric.ball a (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
      (B : Plane → Plane),Continuous B → ∀ B₀ : Plane,
    (∀ y∈Metric.ball a (8*R),‖B y-B₀‖≤η) →
    PlaneWeakGradient (Metric.ball a (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball a ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+256*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2)+
          (A+256)*Real.pi*(8*R)^2*η^2 ∧
      (∫ y in Metric.ball a ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+256*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2)+
          (A+256)*Real.pi*(8*R)^2*η^2 := by
  obtain ⟨A,hA,hreplace⟩ := forced_cmc_replacement_decay
  refine ⟨A,hA,fun p hp hpb p₀ hp₀ a R δ η hR hδ hδ1 hη hosc u G B hB B₀ hBo hg hd ↦ ?_⟩
  obtain ⟨G',he,hn,hint⟩ := L2_translate G a
  have hm := (Lp.memLp u).comp_measurePreserving (measurePreserving_add_right volume a)
  let u' := hm.toLp ((u : Plane → ℝ) ∘ (fun y ↦ y+a))
  have hg' := (hg.comp_add a).congr hm.coeFn_toLp he
  rw [translate_preimage_ball] at hg'
  have hd' := variable_divergence_comp_add (fun _ ↦ ContinuousLinearMap.id ℝ Plane)
    (fun y ↦ cmcJacobian (p y) (G y)-B y) hd a
  rw [translate_preimage_ball] at hd'
  have hp' := hp.comp (show Continuous (fun y : Plane ↦ y+a) from continuous_id.add continuous_const)
  have hB' := hB.comp (show Continuous (fun y : Plane ↦ y+a) from continuous_id.add continuous_const)
  have hd'' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p (y+a)) (G' y)-B (y+a)))=0 := by
    intro ψ hψ hc hs
    rw [← hd' ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]; rfl
  obtain ⟨B',hBe,hBn⟩ := local_divergence_source hB' B₀ (by positivity : 0<8*R) hη
    (fun y hy ↦ hBo (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy))
  have hdf := forced_divergence_localize hp' (fun y ↦ hpb _) G' hB' measurableSet_ball B₀ B' hBe hd''
  obtain ⟨q,hq⟩ := hreplace (fun y ↦ p (y+a)) hp' (fun y ↦ hpb _) p₀ hp₀ R δ hR hδ hδ1
    (fun y hy ↦ hosc (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) u' G' B' hg' hdf
  have hi (s : ℝ) : (∫ y in Metric.ball 0 s,‖G' y‖^2)=
      (∫ y in Metric.ball a s,‖G y‖^2) := by simpa only [sub_zero] using hint s 0
  have hend : (A+256)*‖B'‖^2≤(A+256)*Real.pi*(8*R)^2*η^2 := by
    calc
      _ ≤ (A+256)*(Real.pi*(8*R)^2*η^2) := mul_le_mul_of_nonneg_left hBn (by positivity)
      _ = _ := by ring
  refine ⟨q,fun ρ hρ hρR ↦ ?_⟩
  have hh := hq ρ hρ hρR
  rw [hi ρ,hi (8*R),hint ρ q] at hh
  exact ⟨hh.1.trans (add_le_add le_rfl hend),hh.2.trans (add_le_add le_rfl hend)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_replacement_decay :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball 0 ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+128*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2) ∧
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+128*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cmc_replacement_bounds
  refine ⟨2*Real.pi*C^2,by positivity,fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G hg hd ↦ ?_⟩
  obtain ⟨G',he,hgs,hn⟩ := L2_gradient_truncate G
    (S := Metric.ball (0 : Plane) (8*R)) measurableSet_ball
  have hg' := PlaneWeakGradient.local_congr measurableSet_ball hg EventuallyEq.rfl he
  have hd' := weak_divergence_local_congr measurableSet_ball (fun y ↦ cmcJacobian (p y)) he hd
  obtain ⟨w,W,H,hW,hw,herr,hH,hrep,hb,hl⟩ :=
    hbound p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G' hgs hg' hd'
  have heW : ‖W‖^2≤64*δ^2*‖G'‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg W) herr 2
    nlinarith
  refine ⟨H 0,fun ρ hρ hρR ↦ ?_⟩
  have hρ8 : ρ≤8*R := by linarith
  have heρ := ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρ8)) he
  have heq (q : Plane) : (∫ y in Metric.ball 0 ρ,‖G' y-q‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2) := by
    apply integral_congr_ae
    filter_upwards [heρ] with y hy
    rw [hy]
  have heq0 : (∫ y in Metric.ball 0 ρ,‖G' y‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y‖^2) := by simpa only [sub_zero] using heq 0
  have hh := L2_replacement_energy_decay G' W H hρ hρR (by positivity : 0≤C*R⁻¹*‖G'‖) hrep hb
  have ho := L2_replacement_oscillation_decay G' W H hρ hρR
    (by positivity : 0≤C*R⁻¹^2*‖G'‖) hrep hl
  rw [heq0] at hh
  rw [heq (H 0)] at ho
  constructor
  · calc
      _ ≤ 2*‖W‖^2+2*Real.pi*ρ^2*(C*R⁻¹*‖G'‖)^2 := hh
      _ ≤ 2*(64*δ^2*‖G'‖^2)+2*Real.pi*ρ^2*(C*R⁻¹*‖G'‖)^2 := by linarith
      _ = (2*Real.pi*C^2*(ρ/R)^2+128*δ^2)*‖G'‖^2 := by ring
      _ = _ := by rw [hn]
  · calc
      _ ≤ 2*‖W‖^2+2*Real.pi*(C*R⁻¹^2*‖G'‖)^2*ρ^4 := ho
      _ ≤ 2*(64*δ^2*‖G'‖^2)+2*Real.pi*(C*R⁻¹^2*‖G'‖)^2*ρ^4 := by linarith
      _ = (2*Real.pi*C^2*(ρ/R)^4+128*δ^2)*‖G'‖^2 := by ring
      _ = _ := by rw [hn]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma geometric_modulus_exponent {ρ : ℝ} (hρ : 0<ρ) (hρs : ρ≤1/2) :
    ∃ α : ℝ, 0<α ∧ α≤1 ∧ ρ^α=(1/2:ℝ) := by
  let α := Real.log (1/2:ℝ)/Real.log ρ
  have hρ1 : ρ<1 := by linarith
  have hlog : Real.log ρ<0 := Real.log_neg hρ hρ1
  have hα : 0<α := div_pos_of_neg_of_neg (Real.log_neg (by norm_num) (by norm_num)) hlog
  have hα1 : α≤1 := by
    apply (div_le_iff_of_neg hlog).mpr
    simpa only [one_mul] using Real.log_le_log hρ hρs
  refine ⟨α,hα,hα1,?_⟩
  exact Real.rpow_logb hρ hρ1.ne (by norm_num)

lemma holder_bound_of_geometric_modulus {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} {S : Set X} {ρ R M : ℝ} (hρ : 0<ρ) (hρs : ρ≤1/2)
    (hR : 0<R) (hM : 0≤M)
    (hb : ∀ x∈S, ∀ y∈S, dist x y≤R)
    (hm : ∀ i : ℕ, ∀ x∈S, ∀ y∈S, dist x y≤ρ^i*R →
      dist (f x) (f y)≤M*(1/2:ℝ)^i) :
    ∃ α C : ℝ, 0<α ∧ α≤1 ∧ 0≤C ∧ ∀ x∈S, ∀ y∈S,
      dist (f x) (f y)≤C*(dist x y)^α := by
  obtain ⟨α,hα,hα1,he⟩ := geometric_modulus_exponent hρ hρs
  refine ⟨α,2*M/R^α,hα,hα1,by positivity,?_⟩
  intro x hx y hy
  by_cases hd : dist x y=0
  · have hxy := dist_eq_zero.mp hd
    subst y
    simp only [dist_self,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hdpos : 0<dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  obtain ⟨i,hi,h'i⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hdpos hR) ((div_le_one hR).mpr (hb x hx y hy)) hρ (by linarith : ρ<1)
  have hscale : dist x y≤ρ^i*R := (div_le_iff₀ hR).mp h'i
  have hpow (j : ℕ) : (ρ^j)^α=(1/2:ℝ)^j := by
    rw [← Real.rpow_natCast_mul hρ.le, mul_comm,Real.rpow_mul hρ.le,he,Real.rpow_natCast]
  have hh := Real.rpow_le_rpow (pow_nonneg hρ.le (i+1)) hi.le hα.le
  rw [hpow,Real.div_rpow dist_nonneg hR.le, pow_succ] at hh
  have hc : (1/2:ℝ)^i≤2*(dist x y)^α/R^α := by
    rw [mul_div_assoc]
    linarith
  calc
    _ ≤ M*(1/2:ℝ)^i := hm i x hx y hy hscale
    _ ≤ M*(2*(dist x y)^α/R^α) := mul_le_mul_of_nonneg_left hc hM
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma geometric_energy_decay {E : ℝ → ℝ} {R θ β : ℝ}
    (hR : 0<R) (hER : 0≤E R) (hθ : 0<θ) (hθ1 : θ<1) (hβ : 0≤β)
    (hmono : MonotoneOn E (Ioc 0 R))
    (hdecay : ∀ s : ℝ,0<s → s≤R → E (θ*s)≤θ^β*E s)
    {r : ℝ} (hr : 0<r) (hrR : r≤R) :
    E r≤θ^(-β)*(r/R)^β*E R := by
  have hp (i : ℕ) : E (θ^i*R)≤(θ^β)^i*E R := by
    induction i with
    | zero => simp
    | succ i hi =>
      have hs : θ^i*R≤R := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hR.le
      calc
        _ = E (θ*(θ^i*R)) := by congr 1; ring
        _ ≤ θ^β*E (θ^i*R) := hdecay _ (by positivity) hs
        _ ≤ θ^β*((θ^β)^i*E R) := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hθ.le β)
        _ = _ := by ring
  obtain ⟨i,hi,h'i⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hθ hθ1
  have hs : r≤θ^i*R := (div_le_iff₀ hR).mp h'i
  have hsR : θ^i*R≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hR.le
  have hpow : (θ^β)^(i+1)≤(r/R)^β := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le,mul_comm,
      Real.rpow_mul hθ.le,Real.rpow_natCast]
    exact Real.rpow_le_rpow (pow_nonneg hθ.le _) hi.le hβ
  have hdivide : (θ^β)^i≤θ^(-β)*(r/R)^β := by
    rw [pow_succ] at hpow
    rw [Real.rpow_neg hθ.le]
    have ht : 0<θ^β := Real.rpow_pos_of_pos hθ _
    exact (le_inv_mul_iff₀ ht).mpr (by simpa only [mul_comm] using hpow)
  exact (hmono ⟨hr,hrR⟩ ⟨by positivity,hsR⟩ hs).trans
    ((hp i).trans (mul_le_mul_of_nonneg_right hdivide hER))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma exists_decay_contraction {A β : ℝ} (hA : 0<A) (hβ : 0<β) (hβ2 : β<2) :
    ∃ θ δ₀ : ℝ, 0<θ ∧ θ≤1/16 ∧ 0<δ₀ ∧ δ₀≤1 ∧
      ∀ δ : ℝ,0≤δ → δ≤δ₀ → A*(8*θ)^2+128*δ^2≤θ^β := by
  have hc : ContinuousAt (fun t : ℝ ↦ t^(2-β)) 0 :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
  have he : ∀ᶠ t : ℝ in 𝓝 0,t^(2-β)<(1/2)/(64*A) :=
    hc.eventually_lt continuousAt_const (by
      rw [Real.zero_rpow (by linarith : 2-β≠0)]
      exact div_pos (by norm_num) (mul_pos (by norm_num) hA))
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp he
  let θ : ℝ := min (ε/2) (1/16)
  have hθ : 0<θ := lt_min (half_pos hε) (by norm_num)
  have hθε : θ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hθ1 : θ≤1/16 := min_le_right _ _
  have hsmall : 64*A*θ^(2-β)<1/2 := by
    have hpower : θ^(2-β)<(1/2)/(64*A) :=
      hεs (by simpa [Real.dist_eq,abs_of_pos hθ] using hθε)
    simpa only [mul_comm] using (lt_div_iff₀ (mul_pos (by norm_num) hA)).mp hpower
  let δ₀ : ℝ := Real.sqrt (θ^β/256)
  have htβ : 0<θ^β := Real.rpow_pos_of_pos hθ _
  have hd₀ : 0<δ₀ := Real.sqrt_pos.mpr (by positivity)
  have hd₀1 : δ₀≤1 := Real.sqrt_le_one.mpr (by
    have hpower := Real.rpow_le_one hθ.le (hθ1.trans (by norm_num)) hβ.le
    linarith)
  refine ⟨θ,δ₀,hθ,hθ1,hd₀,hd₀1,fun δ hδ hd ↦ ?_⟩
  have hsquare : δ^2≤θ^β/256 := by
    have hh : δ≤Real.sqrt (θ^β/256) := hd
    have hq := pow_le_pow_left₀ hδ hh 2
    rwa [Real.sq_sqrt (by positivity)] at hq
  have hpow : θ^(2-β)*θ^β=θ^2 := by
    rw [← Real.rpow_add hθ]
    simp
  have hfirst : 64*A*θ^2≤θ^β/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le htβ.le
    rw [mul_assoc,hpow] at hh
    linarith
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_energy_decay {β : ℝ} (hβ : 0<β) (hβ2 : β<2) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ δ₀≤1 ∧
    ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R : ℝ,0<R →
    (∀ y∈Metric.ball 0 R,‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ₀) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball 0 R) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∀ r : ℝ,0<r → r≤R →
      (∫ y in Metric.ball 0 r,‖G y‖^2)≤
        C*(r/R)^β*(∫ y in Metric.ball 0 R,‖G y‖^2) := by
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay
  obtain ⟨θ,δ₀,hθ,hθs,hδ,hδ1,hcontract⟩ := exists_decay_contraction hA hβ hβ2
  refine ⟨θ^(-β),δ₀,Real.rpow_pos_of_pos hθ _,hδ,hδ1,
    fun p hp hpb p₀ hp₀ R hR hosc u G hg hd r hr hrR ↦ ?_⟩
  apply geometric_energy_decay hR (integral_nonneg (fun _ ↦ sq_nonneg _)) hθ
    (by linarith) hβ.le ((plane_L2_energy_mono G).monotoneOn _) ?_ hr hrR
  intro s hs hsR
  have h8 : 8*(s/8)=s := by ring
  have hsub : Metric.ball (0 : Plane) (8*(s/8))⊆Metric.ball 0 R :=
    Metric.ball_subset_ball (by rw [h8]; exact hsR)
  obtain ⟨q,hq⟩ := hreplace p hp hpb p₀ hp₀ (s/8) δ₀ (by positivity)
    hδ.le hδ1 (fun y hy ↦ hosc y (hsub hy)) u G
    (fun v ψ hψ hc hs' ↦ hg v ψ hψ hc (hs'.trans hsub))
    (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
  have hsmall : θ*s ≤ s/8/2 := by nlinarith
  have hh := (hq (θ*s) (by positivity) hsmall).1
  have hratio : θ*s/(s/8)=8*θ := by field_simp
  rw [h8,hratio] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hcontract δ₀ hδ.le le_rfl)
    (integral_nonneg (fun _ ↦ sq_nonneg _)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma linearized_cmc_translate (p : Plane → Plane) (a : Plane) (R : ℝ)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball a R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ (u' : Lp ℝ 2 (volume : Measure Plane)) (G' : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 R) u' G' ∧
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 R →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (p (y+a)) (G' y)))=0) ∧
      ‖G'‖^2=‖G‖^2 ∧
      ∀ r : ℝ,∀ q : Plane,(∫ y in Metric.ball 0 r,‖G' y-q‖^2)=
        (∫ y in Metric.ball a r,‖G y-q‖^2) := by
  obtain ⟨G',he,hn,hint⟩ := L2_translate G a
  have hm := (Lp.memLp u).comp_measurePreserving (measurePreserving_add_right volume a)
  let u' := hm.toLp ((u : Plane → ℝ) ∘ (fun y ↦ y+a))
  have hg' := (hg.comp_add a).congr hm.coeFn_toLp he
  rw [translate_preimage_ball] at hg'
  have hd' := variable_divergence_comp_add (fun y ↦ cmcJacobian (p y)) G hd a
  rw [translate_preimage_ball] at hd'
  refine ⟨u',G',hg',?_,hn,hint⟩
  exact weak_divergence_local_congr measurableSet_ball (fun y ↦ cmcJacobian (p (y+a)))
    (ae_restrict_of_ae he) hd'

theorem cmc_replacement_decay_at :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ (a : Plane) (R δ : ℝ),0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball a (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball a (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball a ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+128*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2) ∧
      (∫ y in Metric.ball a ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+128*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2) := by
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay
  refine ⟨A,hA,fun p hp hpb p₀ hp₀ a R δ hR hδ hδ1 hosc u G hg hd ↦ ?_⟩
  obtain ⟨u',G',hg',hd',hn,hint⟩ := linearized_cmc_translate p a (8*R) u G hg hd
  have hi (s : ℝ) : (∫ y in Metric.ball 0 s,‖G' y‖^2)=
      (∫ y in Metric.ball a s,‖G y‖^2) := by simpa only [sub_zero] using hint s 0
  obtain ⟨q,hq⟩ := hreplace (fun y ↦ p (y+a)) (hp.comp (continuous_id.add continuous_const))
    (fun y ↦ hpb _) p₀ hp₀ R δ hR hδ hδ1
    (fun y hy ↦ hosc (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) u' G' hg' hd'
  refine ⟨q,fun ρ hρ hρR ↦ ?_⟩
  have hh := hq ρ hρ hρR
  rwa [hi ρ,hi (8*R),hint ρ q] at hh

theorem cmc_energy_decay_at {β : ℝ} (hβ : 0<β) (hβ2 : β<2) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ δ₀≤1 ∧
    ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ (a : Plane) (R : ℝ),0<R →
    (∀ y∈Metric.ball a R,‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ₀) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball a R) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∀ r : ℝ,0<r → r≤R →
      (∫ y in Metric.ball a r,‖G y‖^2)≤C*(r/R)^β*‖G‖^2 := by
  obtain ⟨C,δ₀,hC,hδ,hδ1,hdecay⟩ := cmc_energy_decay hβ hβ2
  refine ⟨C,δ₀,hC,hδ,hδ1,fun p hp hpb p₀ hp₀ a R hR hosc u G hg hd r hr hrR ↦ ?_⟩
  obtain ⟨u',G',hg',hd',hn,hint⟩ := linearized_cmc_translate p a R u G hg hd
  have hi (s : ℝ) : (∫ y in Metric.ball 0 s,‖G' y‖^2)=
      (∫ y in Metric.ball a s,‖G y‖^2) := by simpa only [sub_zero] using hint s 0
  have hh := hdecay (fun y ↦ p (y+a)) (hp.comp (continuous_id.add continuous_const))
    (fun y ↦ hpb _) p₀ hp₀ R hR
    (fun y hy ↦ hosc (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) u' G' hg' hd' r hr hrR
  rw [hi r] at hh
  have he : (∫ y in Metric.ball 0 R,‖G' y‖^2)≤‖G‖^2 := by
    rw [← hn,L2_vector_norm_sq_integral]
    exact setIntegral_le_integral (L2_vector_norm_sq_integrable G')
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_left he (by positivity))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma exists_small_power_scale {α ε R : ℝ} (hα : 0<α) (hε : 0<ε)
    (hR : 0<R) (D : ℝ) :
    ∃ r : ℝ,0<r ∧ r≤R ∧ D*r^α≤ε := by
  have hc : ContinuousAt (fun t : ℝ ↦ D*t^α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr hα.le))
  have he : ∀ᶠ t : ℝ in 𝓝 0,D*t^α<ε :=
    hc.eventually_lt continuousAt_const (by simpa [Real.zero_rpow hα.ne'] using hε)
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp he
  let r : ℝ := min (η/2) R
  have hr : 0<r := lt_min (half_pos hη) hR
  refine ⟨r,hr,min_le_right _ _,le_of_lt (hsub ?_)⟩
  have hh : r<η := (min_le_left _ _).trans_lt (by linarith)
  simpa [Real.dist_eq,abs_of_pos hr] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
