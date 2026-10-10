import Mathlib
import OAI.Geometry.CubicTorus.Regularity.SurfaceNormalReverse

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma translateNormal_measurePreserving (μ : FiniteMeasure NormalBundle) (a : Cover) :
    MeasurePreserving (translateNormal a) (μ : Measure NormalBundle)
      (μ.map (translateNormal a) : Measure NormalBundle) :=
  ⟨measurable_translateNormal a,rfl⟩

def normalTranslationLp (μ : FiniteMeasure NormalBundle) (a : Cover)
    (p : ℝ≥0∞) [Fact (1≤p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F p (μ.map (translateNormal a) : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp F p (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ (translateNormal a) (translateNormal_measurePreserving μ a)

lemma normalTranslationLp_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    (p : ℝ≥0∞) [Fact (1≤p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F p (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslationLp μ a p u =ᵐ[(μ : Measure NormalBundle)] u ∘ translateNormal a :=
  Lp.coeFn_compMeasurePreserving u (translateNormal_measurePreserving μ a)

def smoothScalarTranslate (f : smoothPeriodicScalars) (a : Cover) : smoothPeriodicScalars :=
  ⟨fun x => f.val (x+a),f.property.1.comp (contDiff_id.add contDiff_const),by
    intro m x
    simpa only [add_right_comm x (latticeVector m) a] using f.property.2 m (x+a)⟩

lemma gradient_smoothScalarTranslate (f : smoothPeriodicScalars) (a x : Cover) :
    gradient (smoothScalarTranslate f a).val x=gradient f.val (x+a) := by
  simp only [gradient,smoothScalarTranslate,fderiv_comp_add_right]

lemma smoothScalarTranslate_translate_value (f : smoothPeriodicScalars) (a : Cover) (z : NormalBundle) :
    smoothScalarValue (smoothScalarTranslate f a) (translateNormal a z)=smoothScalarValue f z := by
  change (smoothScalarTranslate f a).val (translateNormal a z).1=f.val z.1
  rw [translateNormal_periodic_eval (smoothScalarTranslate f a).property.2]
  change f.val ((z.1 : Cover)-a+a)=f.val z.1
  rw [sub_add_cancel]

lemma smoothScalarTranslate_translate_gradient (f : smoothPeriodicScalars) (a : Cover) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarTranslate f a) (translateNormal a z)=smoothScalarGradient f z := by
  have hp (m : Fin 3 → ℤ) (x : Cover) :
      gradient (smoothScalarTranslate f a).val (x+latticeVector m)=
        gradient (smoothScalarTranslate f a).val x := by
    simp only [gradient,fderiv_periodic (smoothScalarTranslate f a).property.2]
  have hg : gradient (smoothScalarTranslate f a).val (translateNormal a z).1=gradient f.val z.1 := by
    rw [translateNormal_periodic_eval hp,gradient_smoothScalarTranslate,sub_add_cancel]
  change gradient (smoothScalarTranslate f a).val (translateNormal a z).1-
    ⟪(z.2 : Cover),gradient (smoothScalarTranslate f a).val (translateNormal a z).1⟫ • (z.2 : Cover)=_
  rw [hg]
  rfl

def surfaceJetPullTranslation (μ : FiniteMeasure NormalBundle) (a : Cover) :
    SurfaceJet (μ.map (translateNormal a)) →ₗᵢ[ℝ] SurfaceJet μ where
  toLinearMap := (normalTranslationLp μ a 2).toLinearMap.prodMap
    (normalTranslationLp μ a 2).toLinearMap
  norm_map' u := by
    change max ‖normalTranslationLp μ a 2 u.1‖ ‖normalTranslationLp μ a 2 u.2‖=
      max ‖u.1‖ ‖u.2‖
    rw [(normalTranslationLp μ a 2).norm_map,(normalTranslationLp μ a 2).norm_map]

lemma surfaceJetPullTranslation_smooth (μ : FiniteMeasure NormalBundle) (a : Cover)
    (f : smoothPeriodicScalars) :
    surfaceJetPullTranslation μ a (surfaceSmoothJet (μ.map (translateNormal a))
      (smoothScalarTranslate f a))=surfaceSmoothJet μ f := by
  apply Prod.ext
  · apply Lp.ext
    have ha := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarValue (smoothScalarTranslate f a)).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map (translateNormal a) : Measure NormalBundle))
    filter_upwards [normalTranslationLp_ae μ a 2
      (surfaceSmoothJet (μ.map (translateNormal a)) (smoothScalarTranslate f a)).1,ha,
      (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz ha hb
    exact hz.trans (ha.trans ((smoothScalarTranslate_translate_value f a z).trans hb.symm))
  · apply Lp.ext
    have ha := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarGradient (smoothScalarTranslate f a)).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map (translateNormal a) : Measure NormalBundle))
    filter_upwards [normalTranslationLp_ae μ a 2
      (surfaceSmoothJet (μ.map (translateNormal a)) (smoothScalarTranslate f a)).2,ha,
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz ha hb
    exact hz.trans (ha.trans ((smoothScalarTranslate_translate_gradient f a z).trans hb.symm))

lemma smoothScalarTranslate_neg_cancel (f : smoothPeriodicScalars) (a : Cover) :
    smoothScalarTranslate (smoothScalarTranslate f (-a)) a=f := by
  apply Subtype.ext
  funext x
  change f.val (x+a+ -a)=f.val x
  rw [add_neg_cancel_right]

lemma surfaceH1_translation_pull (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet (μ.map (translateNormal a))} (hu : u∈surfaceH1 (μ.map (translateNormal a))) :
    surfaceJetPullTranslation μ a u ∈ surfaceH1 μ := by
  apply map_mem_closure (surfaceJetPullTranslation μ a).continuous hu
  rintro _ ⟨f,rfl⟩
  refine ⟨smoothScalarTranslate f (-a),?_⟩
  have h := surfaceJetPullTranslation_smooth μ a (smoothScalarTranslate f (-a))
  rw [smoothScalarTranslate_neg_cancel] at h
  exact h.symm

theorem surfaceH1_translation_lift (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJetPullTranslation μ a v=u := by
  have hclosed : IsClosed ((surfaceJetPullTranslation μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) :=
    (surfaceJetPullTranslation μ a).isometry.isClosedEmbedding.isClosedMap _ isClosed_closure
  have hsub : Set.range (surfaceSmoothJet μ)⊆(surfaceJetPullTranslation μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a)))) := by
    rintro _ ⟨f,rfl⟩
    exact ⟨surfaceSmoothJet _ (smoothScalarTranslate f a),
      subset_closure (LinearMap.mem_range_self _ _),surfaceJetPullTranslation_smooth μ a f⟩
  exact closure_minimal hsub hclosed hu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjection_translate (a : Cover) (z : NormalBundle) :
    normalProjection (translateNormal a z)=normalProjection z-quotientMap a := by
  change quotientMap (representative (quotientMap z.1-quotientMap a))=_
  rw [quotientMap_representative]
  rfl

lemma normalTranslationLp_multiplier (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (u : Lp ℝ 2 (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslationLp μ a 2 (surfaceMultiplier (μ.map (translateNormal a)) q u)=
      surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u) := by
  apply Lp.ext
  have hm := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_lpSMul (r := 2) q u)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u),
    normalTranslationLp_ae μ a ∞ q,normalTranslationLp_ae μ a 2 u,
    normalTranslationLp_ae μ a 2 (surfaceMultiplier (μ.map (translateNormal a)) q u),hm]
      with z hz hq hu hv hm
  change (surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u)) z=_ at hz
  change surfaceMultiplier (μ.map (translateNormal a)) q u (translateNormal a z)=_ at hm
  simp only [Function.comp_apply,smul_eq_mul,Pi.mul_apply] at hz hq hu hv hm
  rw [hv,hm,hz,hq,hu]

lemma surfaceJacobiB_translation_pull (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (u v : SurfaceJet (μ.map (translateNormal a))) :
    surfaceJacobiB μ (normalTranslationLp μ a ∞ q)
      (surfaceJetPullTranslation μ a u) (surfaceJetPullTranslation μ a v)=
        surfaceJacobiB (μ.map (translateNormal a)) q u v := by
  change ⟪normalTranslationLp μ a 2 u.2,normalTranslationLp μ a 2 v.2⟫-
    ⟪surfaceMultiplier μ (normalTranslationLp μ a ∞ q) (normalTranslationLp μ a 2 u.1),
      normalTranslationLp μ a 2 v.1⟫=_
  rw [← normalTranslationLp_multiplier,
    (normalTranslationLp μ a 2 (F := Cover)).inner_map_map u.2 v.2,
    (normalTranslationLp μ a 2 (F := ℝ)).inner_map_map
      (surfaceMultiplier (μ.map (translateNormal a)) q u.1) v.1]
  rfl

lemma surfaceCurvatureLp_translation (μ : FiniteMeasure NormalBundle) (a : Cover)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    normalTranslationLp μ a ∞
      (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
        (hN.comp (contDiff_id.add contDiff_const)))=surfaceCurvatureLp μ N hN := by
  apply Lp.ext
  let Q : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩
  let Q' : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous (N := fun x => N (x+a))
      (hN.comp (contDiff_id.add contDiff_const))).comp
      (continuous_subtype_val.comp continuous_fst)⟩
  have hqp (m : Fin 3 → ℤ) (x : Cover) :
      coverTrace ((fderiv ℝ N (x+latticeVector m+a)).comp (fderiv ℝ N (x+latticeVector m+a)))=
        coverTrace ((fderiv ℝ N (x+a)).comp (fderiv ℝ N (x+a))) := by
    rw [add_right_comm,fderiv_periodic hp]
  have he (z : NormalBundle) : Q' (translateNormal a z)=Q z := by
    change coverTrace ((fderiv ℝ (fun x => N (x+a)) (translateNormal a z).1).comp
      (fderiv ℝ (fun x => N (x+a)) (translateNormal a z).1))=_
    simp only [fderiv_comp_add_right]
    rw [translateNormal_periodic_eval (F := fun x =>
      coverTrace ((fderiv ℝ N (x+a)).comp (fderiv ℝ N (x+a)))) hqp,sub_add_cancel]
    rfl
  have hq := (translateNormal_measurePreserving μ a).quasiMeasurePreserving.ae_eq_comp
    (Q'.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ.map (translateNormal a) : Measure NormalBundle))
  filter_upwards [normalTranslationLp_ae μ a ∞
    (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
      (hN.comp (contDiff_id.add contDiff_const))),hq,
    Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz hq hr
  exact hz.trans (hq.trans ((he z).trans hr.symm))

theorem surfaceH1_jacobi_translation_lift (μ : FiniteMeasure NormalBundle) (a : Cover)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hh : ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) :
    ∃ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJetPullTranslation μ a v=u ∧
      ∀ w∈surfaceH1 (μ.map (translateNormal a)),
        surfaceJacobiB (μ.map (translateNormal a))
          (surfaceCurvatureLp (μ.map (translateNormal a)) (fun x => N (x+a))
            (hN.comp (contDiff_id.add contDiff_const))) v w=0 := by
  obtain ⟨v,hv,he⟩ := surfaceH1_translation_lift μ a hu
  refine ⟨v,hv,he,?_⟩
  intro w hw
  rw [← surfaceJacobiB_translation_pull,surfaceCurvatureLp_translation μ a N hN hp,he]
  exact hh _ (surfaceH1_translation_pull μ a hw)

lemma surfaceH1_translation_value (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} {v : SurfaceJet (μ.map (translateNormal a))}
    (he : surfaceJetPullTranslation μ a v=u)
    {F : Torus → ℝ} (hF : Measurable F)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    (v.1 : NormalBundle → ℝ)=ᵐ[(μ.map (translateNormal a) : Measure NormalBundle)]
      (fun x => F (x+quotientMap a)) ∘ normalProjection := by
  change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),
    v.1 z=F (normalProjection z+quotientMap a)
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable v.1).measurable
      (hF.comp (normalProjection_continuous.measurable.add measurable_const)))).mpr
  have hs := normalTranslationLp_ae μ a 2 v.1
  have he1 : normalTranslationLp μ a 2 v.1=u.1 := congrArg Prod.fst he
  rw [he1] at hs
  filter_upwards [hs,hFu] with z hz hf
  simp only [Function.comp_apply] at hz hf
  change v.1 (translateNormal a z)=F (normalProjection (translateNormal a z)+quotientMap a)
  rw [← hz,hf,normalProjection_translate,sub_add_cancel]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_H1_jacobi_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0<s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ z∈Metric.ball (0 : Cover) s,
        quotientMap (x+z)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n z)=z) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+normalGraph n f y))) 0 := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have he (z : Cover) : cubeCenter+z+a=x+z := by dsimp [a]; abel
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    dsimp [a]; congr 1; abel
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hNu' (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E')) :
      ∀ᶠ z in 𝓝 y,‖N' z‖=1 := by
    rw [frontier_openRepresentative_translation hE] at hy
    have hy' : quotientMap (y+a)∈frontier (openRepresentative E) := by
      simpa only [mem_preimage,quotientMap_add] using hy
    exact (continuous_add_const a).continuousAt.eventually (hNu (y+a) hy')
  let F' : Torus → ℝ := fun z => F (z+quotientMap a)
  have hF' : ContinuousOn F' (frontier (openRepresentative E')) := by
    apply hF.comp (continuous_add_const _).continuousOn
    intro z hz
    rwa [frontier_openRepresentative_translation hE] at hz
  obtain ⟨v,hv,hpull,hvh⟩ := surfaceH1_jacobi_translation_lift μ a N hN hp hu hhom
  have hvF : (v.1 : NormalBundle → ℝ)=ᵐ[(μ.map (translateNormal a) : Measure NormalBundle)]
      F' ∘ normalProjection := surfaceH1_translation_value μ a hpull hFm hFu
  obtain ⟨n,f,s,hn,hs,hf0,hf,hin,hcover,hreg⟩ :=
    isMinimizerAt_centered_H1_jacobi_smooth hV hE' hmin' hc
      (isNormalMeasure_translation hE hμ a) N' hN' hae' hNu' hv hvh hF' hvF
  refine ⟨n,f,s,hn,hs,hf0,hf,?_,?_,?_⟩
  · intro y hy
    have hi := hin y hy
    rw [frontier_openRepresentative_translation hE] at hi
    simpa only [mem_preimage,← quotientMap_add,he] using hi
  · intro z hz
    have hc' := hcover z hz
    rw [frontier_openRepresentative_translation hE] at hc'
    simpa only [mem_preimage,← quotientMap_add,he] using hc'
  · simpa only [F',← quotientMap_add,he] using hreg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeFrameOperator (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (f : Plane → ℝ) (x : Plane) : ℝ :=
  (∑ i,⟪fderiv ℝ (gradient f) x (B x i),B x i⟫)+⟪gradient f x,b x⟫

lemma smooth_line_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) (t : ℝ) :
    deriv (fun s : ℝ => f (x+s • v)) t= fderiv ℝ f (x+t • v) v := by
  simpa only [Function.comp_def,id_eq,one_smul] using ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const v |>.const_add x)).deriv

lemma smooth_line_second_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) :
    deriv (deriv (fun s : ℝ => f (x+s • v))) 0=
      ⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have he : deriv (fun s : ℝ => f (x+s • v))=
      (fun t => fderiv ℝ f (x+t • v) v) := funext (smooth_line_deriv hf x v)
  rw [he]
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) :=
    hf.fderiv_right (by simp) |>.clm_apply contDiff_const
  rw [smooth_line_deriv hg x v 0]
  simp only [zero_smul,add_zero]
  rw [plane_hessian_direction hf,inner_gradient_left]

lemma plane_hessian_nonneg_of_local_min {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane} (hm : IsLocalMin f x) (v : Plane) :
    0≤⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (show Continuous (fun t : ℝ => x+t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
  have hm' : IsLocalMin (fun t : ℝ => f (x+t • v)) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), f (x+0 • v)≤f (x+t • v)
    simpa only [zero_smul,add_zero] using ht.eventually hm
  rw [← smooth_line_second_deriv hf x v]
  exact second_derivative_nonneg_of_local_min hm'
    (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt

lemma planeFrameOperator_nonneg_of_local_min (B : Plane → Fin 2 → Plane)
    (b : Plane → Plane) {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} (hm : IsLocalMin f x) : 0≤planeFrameOperator B b f x := by
  have hz : gradient f x=0 := by simp [gradient,hm.fderiv_eq_zero]
  simp only [planeFrameOperator,hz,inner_zero_left,add_zero]
  exact Finset.sum_nonneg (fun i _ => plane_hessian_nonneg_of_local_min hf hm (B x i))

lemma planeFrameOperator_sub (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f g : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Plane) : planeFrameOperator B b (fun y => f y-g y) x=
      planeFrameOperator B b f x-planeFrameOperator B b g x := by
  have he : gradient (fun y => f y-g y)=fun y => gradient f y-gradient g y := by
    funext y
    simp only [gradient,fderiv_fun_sub (hf.differentiable (by simp) y)
      (hg.differentiable (by simp) y),map_sub]
  rw [planeFrameOperator,he,fderiv_fun_sub
    ((plane_gradient_contDiff hf).differentiable (by simp) x)
    ((plane_gradient_contDiff hg).differentiable (by simp) x)]
  simp only [sub_apply,inner_sub_left,Finset.sum_sub_distrib,planeFrameOperator]
  ring

lemma planeFrameOperator_smul (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x : Plane) :
    planeFrameOperator B b (fun y => c*f y) x=c*planeFrameOperator B b f x := by
  have he : gradient (fun y => c*f y)=fun y => c • gradient f y := by
    funext y
    simp only [gradient,show (fun y => c*f y)=(fun y => c • f y) from rfl,
      fderiv_fun_const_smul (hf.differentiable (by simp) y),map_smul]
  rw [planeFrameOperator,he,fderiv_fun_const_smul
    ((plane_gradient_contDiff hf).differentiable (by simp) x)]
  simp only [smul_apply,real_inner_smul_left,← Finset.mul_sum,planeFrameOperator]
  ring

theorem planeFrameOperator_annulus_comparison (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : Plane) {r R : ℝ} (hr : 0<r) (hrR : r<R)
    (hbd : ∀ x,‖x-c‖=r ∨ ‖x-c‖=R → 0≤f x)
    (hL : ∀ x,r<‖x-c‖ → ‖x-c‖<R → planeFrameOperator B b f x<0) :
    ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤f x := by
  let K : Set Plane := Metric.closedBall c R \ Metric.ball c r
  have hK : IsCompact K := (isCompact_closedBall c R).diff Metric.isOpen_ball
  have hKne : K.Nonempty := by
    obtain ⟨point,hpoint⟩ := (NormedSpace.sphere_nonempty (x := c)).2 hr.le
    have hdist : dist point c=r := hpoint
    refine ⟨point,?_⟩
    change dist point c≤R ∧ ¬ dist point c<r
    rw [hdist]
    exact ⟨hrR.le,lt_irrefl r⟩
  intro x hrx hxR
  have hxK : x∈K := by simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,
    not_lt] using And.intro hxR hrx
  obtain ⟨y,hyK,hym⟩ := hK.exists_isMinOn hKne hf.continuous.continuousOn
  have hyr : r≤‖y-c‖ := by simpa only [K,Set.mem_sdiff,Metric.mem_ball,dist_eq_norm,not_lt] using hyK.2
  have hyR : ‖y-c‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hyK.1
  have hy0 : 0≤f y := by
    by_cases h1 : ‖y-c‖=r
    · exact hbd y (Or.inl h1)
    by_cases h2 : ‖y-c‖=R
    · exact hbd y (Or.inr h2)
    have hri : r<‖y-c‖ := lt_of_le_of_ne hyr (Ne.symm h1)
    have hRi : ‖y-c‖<R := lt_of_le_of_ne hyR h2
    have hn : K∈𝓝 y := by
      have ho : IsOpen {z : Plane | r<‖z-c‖ ∧ ‖z-c‖<R} :=
        (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
      apply mem_of_superset (ho.mem_nhds ⟨hri,hRi⟩)
      intro z hz
      simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,not_lt] using
        And.intro hz.2.le hz.1.le
    have hm : IsLocalMin f y := hym.isLocalMin hn
    exact False.elim ((not_lt_of_ge (planeFrameOperator_nonneg_of_local_min B b hf hm))
      (hL y hri hRi))
  exact hy0.trans (hym hxK)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev PlaneSmooth (f : Plane → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

lemma planeDivergence_sub {F G : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Plane) :
    planeDivergence (fun y => F y-G y) x=planeDivergence F x-planeDivergence G x := by
  simp only [planeDivergence,fderiv_fun_sub (hF.differentiable (by simp) x)
    (hG.differentiable (by simp) x),sub_apply,PiLp.sub_apply]
  ring

lemma planeDivergence_contDiff {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : PlaneSmooth (planeDivergence F) := by
  unfold planeDivergence
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const))

def planeElliptic (A : Plane → Plane →L[ℝ] Plane) (f : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun x => A x (gradient f x))

def planeDrift (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  fderiv ℝ f x (b x)

lemma planeElliptic_contDiff {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) : PlaneSmooth (planeElliptic A f) :=
  planeDivergence_contDiff (hA.clm_apply (plane_gradient_contDiff hf))

lemma planeDrift_contDiff {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : PlaneSmooth f) : PlaneSmooth (planeDrift b f) :=
  (hf.fderiv_right (by simp)).clm_apply hb

lemma planeDrift_compact {b : Plane → Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeDrift b f) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDrift,hz])

lemma planeDivergence_compact {F : Plane → Plane} (hc : HasCompactSupport F) :
    HasCompactSupport (planeDivergence F) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDivergence,hz])

lemma planeElliptic_compact {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeElliptic A f) := by
  apply planeDivergence_compact
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [hz])

lemma planeDivergence_integral_zero {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    (∫ x,planeDivergence F x)=0 := by
  have hcomp (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hcc (i : Fin 2) : HasCompactSupport (fun y => F y i) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hi (i : Fin 2) : Integrable (fun y => fderiv ℝ (fun z => F z i) y
      (EuclideanSpace.single i 1)) :=
    (((hcomp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcc i).fderiv_apply ℝ _)
  have hp (i : Fin 2) := C1_local_integration_by_parts (g := fun _ : Plane => (1:ℝ)) isOpen_univ continuous_const
    contDiffOn_const ((hcomp i).of_le (by simp)) (hcc i)
    (subset_univ _) (EuclideanSpace.single i 1)
  simp only [fderiv_fun_const,one_mul] at hp
  simp only [plane_component_fderiv (hF.of_le (by simp))] at hi hp
  have hz (i : Fin 2) : (∫ y, ((fderiv ℝ F y) (EuclideanSpace.single i 1)) i)=0 := by
    simpa using (hp i).symm
  simp only [planeDivergence]
  rw [integral_add (hi 0) (hi 1),hz 0,hz 1,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeEnergy (A : Plane → Plane →L[ℝ] Plane) (u : Plane → ℝ) (x : Plane) : ℝ :=
  ⟪gradient u x,A x (gradient u x)⟫

lemma planeEnergy_contDiff {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) : PlaneSmooth (planeEnergy A u) :=
  (plane_gradient_contDiff hu).inner ℝ (hA.clm_apply (plane_gradient_contDiff hu))

lemma planeEnergy_compact {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hc : HasCompactSupport u) : HasCompactSupport (planeEnergy A u) := by
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [planeEnergy,hz])

lemma planeEnergy_fderiv {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x v : Plane) :
    fderiv ℝ (planeEnergy A u) x v=
      2*⟪fderiv ℝ (gradient u) x v,A x (gradient u x)⟫+
      ⟪gradient u x,(fderiv ℝ A x v) (gradient u x)⟫ := by
  have hg := (plane_gradient_contDiff hu).differentiable (by simp) x
  have ha := hA.differentiable (by simp) x
  unfold planeEnergy
  rw [fderiv_inner_apply ℝ hg (ha.clm_apply hg),fderiv_clm_apply ha hg]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,inner_add_right]
  rw [hAs x (gradient u x) (fderiv ℝ (gradient u) x v)]
  ring

lemma planeDrift_fderiv {b : Plane → Plane} {u : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) (x v : Plane) :
    fderiv ℝ (planeDrift b u) x v=
      ⟪fderiv ℝ (gradient u) x (b x),v⟫+⟪gradient u x,fderiv ℝ b x v⟫ := by
  have he : planeDrift b u=fun y => ⟪gradient u y,b y⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [he,fderiv_inner_apply ℝ ((plane_gradient_contDiff hu).differentiable (by simp) x)
    (hb.differentiable (by simp) x),plane_hessian_symmetric hu]
  rw [real_inner_comm v]
  ring

def planeRellichFlux (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (u : Plane → ℝ) (x : Plane) : Plane :=
  (2*planeDrift b u x+planeDivergence b x*u x) • A x (gradient u x)-
    planeEnergy A u x • b x-
    ((1/2:ℝ)*u x^2) • A x (gradient (planeDivergence b) x)

lemma planeRellichFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) :
    ContDiff ℝ (⊤ : ℕ∞) (planeRellichFlux A b u) :=
  ((((contDiff_const.mul (planeDrift_contDiff hb hu)).add
    ((planeDivergence_contDiff hb).mul hu)).smul
      (hA.clm_apply (plane_gradient_contDiff hu))).sub
    ((planeEnergy_contDiff hA hu).smul hb)).sub
    ((contDiff_const.mul (hu.pow 2)).smul
      (hA.clm_apply (plane_gradient_contDiff (planeDivergence_contDiff hb))))

lemma planeRellichFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (planeRellichFlux A b u) := by
  apply (((planeDrift_compact (b := b) hc).mul_left.add hc.mul_left).smul_right.sub
    (planeEnergy_compact hc).smul_right).sub
  have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  exact hpow.mul_left.smul_right

theorem planeRellichFlux_divergence {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeDivergence (planeRellichFlux A b u) x=
      planeElliptic A u x*(2*planeDrift b u x+planeDivergence b x*u x)+
      2*⟪gradient u x,fderiv ℝ b x (A x (gradient u x))⟫-
      ⟪gradient u x,(fderiv ℝ A x (b x)) (gradient u x)⟫-
      (1/2:ℝ)*planeElliptic A (planeDivergence b) x*u x^2 := by
  have hd := planeDivergence_contDiff hb
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hD := hA.clm_apply (plane_gradient_contDiff hd)
  have hK : PlaneSmooth (fun y => 2*planeDrift b u y+planeDivergence b y*u y) :=
    (contDiff_const.mul (planeDrift_contDiff hb hu)).add (hd.mul hu)
  have hE := planeEnergy_contDiff hA hu
  have hW : PlaneSmooth (fun y => (1/2:ℝ)*u y^2) := contDiff_const.mul (hu.pow 2)
  unfold planeRellichFlux
  erw [planeDivergence_sub ((hK.smul hG).sub (hE.smul hb)) (hW.smul hD),
    planeDivergence_sub (hK.smul hG) (hE.smul hb),
    planeDivergence_smul (hK.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hE.differentiable (by simp) x) (hb.differentiable (by simp) x),
    planeDivergence_smul (hW.differentiable (by simp) x) (hD.differentiable (by simp) x)]
  simp only [inner_gradient_left]
  rw [fderiv_fun_add ((contDiff_const.mul (planeDrift_contDiff hb hu)).differentiable (by simp) x)
      ((hd.mul hu).differentiable (by simp) x),
    fderiv_const_mul ((planeDrift_contDiff hb hu).differentiable (by simp) x),
    fderiv_fun_mul (hd.differentiable (by simp) x) (hu.differentiable (by simp) x),
    fderiv_const_mul ((hu.pow 2).differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [planeDrift_fderiv hb hu,planeEnergy_fderiv hA hu hAs]
  simp only [← inner_gradient_left,planeElliptic,planeEnergy]
  rw [hAs x (gradient u x) (gradient (planeDivergence b) x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCarlemanS (A : Plane → Plane →L[ℝ] Plane) (q : Plane → ℝ)
    (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ := planeElliptic A u x+τ^2*q x*u x

def planeCarlemanT (b : Plane → Plane) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ :=
  -τ*(2*planeDrift b u x+planeDivergence b x*u x)

def planeCarlemanP (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ :=
  planeCarlemanS A q τ u x+planeCarlemanT b τ u x

def planeCarlemanR (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (x w : Plane) : ℝ := 4*⟪w,fderiv ℝ b x (A x w)⟫-
      2*⟪w,(fderiv ℝ A x (b x)) w⟫

def planeCarlemanFlux (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : Plane :=
  (2*τ) • planeRellichFlux A b u x+(2*τ^3*q x*u x^2) • b x

lemma planeCarlemanFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeCarlemanFlux A b q τ u) :=
  by
  unfold planeCarlemanFlux
  exact ((planeRellichFlux_contDiff hA hb hu).const_smul (2*τ)).add
    ((((contDiff_const (c := 2*τ^3)).mul hq).mul (hu.pow 2)).smul hb)

lemma planeCarlemanFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanFlux A b q τ u) := by
  unfold planeCarlemanFlux
  apply HasCompactSupport.add
  · apply (planeRellichFlux_compact (A := A) (b := b) hc).mono
    intro x hx hz
    exact hx (by simp only [hz,smul_zero])
  · have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
      intro x hx hz
      exact hx (by simp [hz]))
    exact hpow.mul_left.smul_right

lemma planeCarlemanP_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    PlaneSmooth (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_contDiff hA hu).add ((contDiff_const.mul hq).mul hu)).add
    (contDiff_const.mul ((contDiff_const.mul (planeDrift_contDiff hb hu)).add
      ((planeDivergence_contDiff hb).mul hu)))

lemma planeCarlemanP_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_compact hc).add hc.mul_left).add
    (((planeDrift_compact hc).mul_left.add hc.mul_left).mul_left)

theorem planeCarleman_pointwise {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) (x : Plane) :
    (planeCarlemanP A b q τ u x)^2+planeDivergence (planeCarlemanFlux A b q τ u) x=
      (planeCarlemanS A q τ u x)^2+(planeCarlemanT b τ u x)^2+
      τ*planeCarlemanR A b x (gradient u x)+
      (2*τ^3*planeDrift b q x-τ*planeElliptic A (planeDivergence b) x)*u x^2 := by
  have hf := planeRellichFlux_contDiff hA hb hu
  have hk : PlaneSmooth (fun y => 2*τ^3*q y*u y^2) :=
    (contDiff_const.mul hq).mul (hu.pow 2)
  unfold planeCarlemanFlux
  erw [planeDivergence_add ((hf.const_smul (2*τ)).differentiable (by simp) x)
      ((hk.smul hb).differentiable (by simp) x),
    planeDivergence_smul (differentiableAt_const (2*τ)) (hf.differentiable (by simp) x),
    planeDivergence_smul (hk.differentiable (by simp) x) (hb.differentiable (by simp) x)]
  simp only [add_zero,inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply]
  rw [planeRellichFlux_divergence hA hb hu hAs,
    fderiv_fun_mul ((contDiff_const.mul hq).differentiable (by simp) x)
      ((hu.pow 2).differentiable (by simp) x),
    fderiv_const_mul (hq.differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  simp only [planeCarlemanP,planeCarlemanS,planeCarlemanT,planeCarlemanR,planeDrift]
  ring

theorem planeCarleman_integral {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hc : HasCompactSupport u) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) :
    (∫ x,(planeCarlemanP A b q τ u x)^2)=
      ∫ x,(planeCarlemanS A q τ u x)^2+(planeCarlemanT b τ u x)^2+
      τ*planeCarlemanR A b x (gradient u x)+
      (2*τ^3*planeDrift b q x-τ*planeElliptic A (planeDivergence b) x)*u x^2 := by
  have hp := planeCarlemanP_contDiff hA hb hq hu τ
  have hpc := planeCarlemanP_compact (A := A) (b := b) (q := q) hc τ
  have hi : Integrable (fun x => (planeCarlemanP A b q τ u x)^2) :=
    (hp.continuous.pow 2).integrable_of_hasCompactSupport (hpc.mono (by
      intro x hx hz
      exact hx (by simp [hz])))
  have hf := planeCarlemanFlux_contDiff hA hb hq hu τ
  have hfc := planeCarlemanFlux_compact (A := A) (b := b) (q := q) hc τ
  have hd : Integrable (planeDivergence (planeCarlemanFlux A b q τ u)) :=
    (planeDivergence_contDiff hf).continuous.integrable_of_hasCompactSupport
    (planeDivergence_compact hfc)
  simp_rw [← planeCarleman_pointwise hA hb hq hu hAs τ]
  rw [integral_add hi hd,planeDivergence_integral_zero hf hfc,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma carleman_scalar_coercivity {C D Q c τ E R S T z q d l : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ)
    (hpseudo : 2≤2*c-(C+1)*Q) (hR : -C*E≤R) (hq : q≤Q)
    (hd : c≤d) (hl : l≤D) :
    τ*E+τ^3*z^2≤S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E) := by
  have ht : 0≤τ := by linarith
  have ha : 0≤C+1 := by linarith
  have ht2 : τ≤τ^2 := by nlinarith
  have hb : 0≤τ^3-D*τ-(C+1)^2*τ^2 := by
    have h₁ := mul_le_mul_of_nonneg_left ht2 hD
    have h₂ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg τ)
    nlinarith
  have hs : 0≤S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2 := by
    nlinarith only [sq_nonneg (S+(C+1)*τ*z),sq_nonneg S,
      sq_nonneg ((C+1)*τ*z)]
  have h₁ : 0≤τ*(R+C*E) := mul_nonneg ht (by linarith)
  have h₂ : 0≤(2*τ^3*(d-c))*z^2 :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hd)) (sq_nonneg z)
  have h₃ : 0≤((C+1)*τ^3*(Q-q))*z^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg ht _)) (sub_nonneg.mpr hq)) (sq_nonneg z)
  have h₄ : 0≤(τ*(D-l))*z^2 :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hl)) (sq_nonneg z)
  have h₅ : 0≤(τ^3*(2*c-(C+1)*Q-2))*z^2 :=
    mul_nonneg (mul_nonneg (pow_nonneg ht _) (by linarith)) (sq_nonneg z)
  have h₆ := mul_nonneg hb (sq_nonneg z)
  have he : S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E)-(τ*E+τ^3*z^2)=
      T^2+(S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2)+τ*(R+C*E)+
      (2*τ^3*(d-c))*z^2+((C+1)*τ^3*(Q-q))*z^2+
      (τ*(D-l))*z^2+(τ^3*(2*c-(C+1)*Q-2))*z^2+
      (τ^3-D*τ-(C+1)^2*τ^2)*z^2 := by ring
  have hh := add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (sq_nonneg T) hs) h₁) h₂) h₃) h₄) h₅) h₆
  rw [← he] at hh
  exact sub_nonneg.mp hh

structure PlaneCarlemanData (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (U : Set Plane) (C D Q c : ℝ) : Prop where
  C_nonneg : 0≤C
  D_nonneg : 0≤D
  pseudoconvex : 2≤2*c-(C+1)*Q
  principal : ∀ x∈U,∀ w,-C*⟪w,A x w⟫≤planeCarlemanR A b x w
  weight_bound : ∀ x∈U,q x≤Q
  transport_bound : ∀ x∈U,c≤planeDrift b q x
  remainder_bound : ∀ x∈U,planeElliptic A (planeDivergence b) x≤D

lemma plane_energy_flux_divergence {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) (x : Plane) :
    planeDivergence (fun y => u y • A y (gradient u y)) x=
      u x*planeElliptic A u x+planeEnergy A u x := by
  exact planeDivergence_smul (hu.differentiable (by simp) x)
    ((hA.clm_apply (plane_gradient_contDiff hu)).differentiable (by simp) x)

theorem planeCarleman_coercive {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hc : HasCompactSupport u) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport u⊆U)
    (hdata : PlaneCarlemanData A b q U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    (∫ x,τ*planeEnergy A u x+τ^3*u x^2)≤
      ∫ x,(planeCarlemanP A b q τ u x)^2 := by
  let F : Plane → Plane := fun x => planeCarlemanFlux A b q τ u x+
    ((C+1)*τ) • (u x • A x (gradient u x))
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hf : ContDiff ℝ (⊤ : ℕ∞) F :=
    (planeCarlemanFlux_contDiff hA hb hq hu τ).add ((hu.smul hG).const_smul ((C+1)*τ))
  have hgc : HasCompactSupport (fun x => ((C+1)*τ) • (u x • A x (gradient u x))) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hfc : HasCompactSupport F :=
    (planeCarlemanFlux_compact (A := A) (b := b) (q := q) hc τ).add hgc
  have hdiv (x : Plane) : planeDivergence F x=
      planeDivergence (planeCarlemanFlux A b q τ u) x+
        (C+1)*τ*(u x*planeElliptic A u x+planeEnergy A u x) := by
    dsimp only [F]
    erw [planeDivergence_add ((planeCarlemanFlux_contDiff hA hb hq hu τ).differentiable (by simp) x)
        (((hu.smul hG).const_smul ((C+1)*τ)).differentiable (by simp) x),
      planeDivergence_smul (differentiableAt_const ((C+1)*τ)) ((hu.smul hG).differentiable (by simp) x)]
    simp only [inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply,add_zero]
    erw [plane_energy_flux_divergence hA hu]
  have hpoint (x : Plane) : τ*planeEnergy A u x+τ^3*u x^2≤
      (planeCarlemanP A b q τ u x)^2+planeDivergence F x := by
    rw [hdiv,← add_assoc,planeCarleman_pointwise hA hb hq hu hAs τ]
    by_cases hx : x∈tsupport u
    · have hh := carleman_scalar_coercivity hdata.C_nonneg hdata.D_nonneg hτ hbudget
        hdata.pseudoconvex (hdata.principal x (hs hx) (gradient u x))
        (hdata.weight_bound x (hs hx)) (hdata.transport_bound x (hs hx))
        (hdata.remainder_bound x (hs hx))
        (S := planeCarlemanS A q τ u x) (T := planeCarlemanT b τ u x) (z := u x)
      simpa only [planeEnergy,planeCarlemanS,add_sub_cancel_right] using hh
    · have hz : u x=0 := image_eq_zero_of_notMem_tsupport hx
      have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp only [planeEnergy,hg,inner_zero_left,mul_zero,hz,zero_pow (by decide : (2:ℕ)≠0),
        planeCarlemanR,map_zero,sub_self,add_zero,zero_mul]
      positivity
  have huc : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  have hi : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact hc)).const_mul τ).add
      (((hu.continuous.pow 2).integrable_of_hasCompactSupport huc).const_mul (τ^3))
  have hp := planeCarlemanP_contDiff hA hb hq hu τ
  have hpc := planeCarlemanP_compact (A := A) (b := b) (q := q) hc τ
  have hj : Integrable (fun x => (planeCarlemanP A b q τ u x)^2) :=
    (hp.continuous.pow 2).integrable_of_hasCompactSupport (hpc.mono (by
      intro x hx hz
      exact hx (by simp [hz])))
  have hk : Integrable (planeDivergence F) :=
    (planeDivergence_contDiff hf).continuous.integrable_of_hasCompactSupport
    (planeDivergence_compact hfc)
  have hm := integral_mono hi (hj.add hk) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add hj hk,planeDivergence_integral_zero hf hfc,add_zero] at hm
  exact hm

end CubicTorus

end
end

end OAI
