import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
lemma lip_comp_memLp_finite [IsFiniteMeasure μ] {p : ℝ≥0∞} {f : α → E}
    {g : E → F} {K : ℝ≥0} (hg : LipschitzWith K g) (hf : MemLp f p μ) :
    MemLp (g ∘ f) p μ := by
  have h := ((hg.sub (LipschitzWith.const (g 0))).comp_memLp (by simp) hf).add (memLp_const (g 0))
  convert h using 1
  ext x
  simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]
end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma memLp_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    MemLp (fun x => F (r x,f x)) 2 (MassMeasure.currentMassMeasure hT) := by
  let : IsFiniteMeasure (MassMeasure.currentMassMeasure hT) := by
    rw [←q.map_atlasMeasure]
    infer_instance
  exact lip_comp_memLp_finite hF (MemLp.of_fst_snd
    ⟨((Foundations.boundedLip_of_lipschitz hr).memLp 2), (Lp.memLp f)⟩)

noncomputable def bivariateValue {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) : Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (q.memLp_bivariate hr hF f).toLp (fun x => F (r x,f x))

lemma bivariateValue_ae {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    q.bivariateValue hr hF f =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => F (r x,f x)) :=
  (q.memLp_bivariate hr hF f).coeFn_toLp

lemma lipschitz_bivariateValue {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F) :
    LipschitzWith B (q.bivariateValue hr hF) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (q.bivariateValue hr hF f) (q.bivariateValue hr hF g),
    Lp.coeFn_sub f g,q.bivariateValue_ae hr hF f,q.bivariateValue_ae hr hF g] with x h1 h2 h3 h4
  rw [h1,h2,Pi.sub_apply,Pi.sub_apply,h3,h4]
  simpa only [←dist_eq_norm,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
    hF.dist_le_mul (r x,f x) (r x,g x)

lemma bivariateValue_value {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F) :
    q.bivariateValue hr hF (value hu) = value (hF.comp (hr.prodMk hu)) := by
  apply Lp.ext
  filter_upwards [q.bivariateValue_ae hr hF (value hu),
    ((Foundations.boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp,
    ((Foundations.boundedLip_of_lipschitz (hF.comp (hr.prodMk hu))).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x h1 h2 h3
  change q.bivariateValue hr hF (value hu) x = _ at h1
  change value (hT := hT) hu x = _ at h2
  change value (hT := hT) (hF.comp (hr.prodMk hu)) x = _ at h3
  rw [h1,h2,h3]
  rfl

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
noncomputable def binaryDerivative (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ
lemma binaryDerivative_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (L M : E →L[ℝ] ℝ) :
    (binaryDerivative a b).comp (L.prod M) = a • L+b • M := by
  ext z
  simp [binaryDerivative]
end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_bivariate {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t) :
    q.gradientFunction (fun x => F (r x,u x)) =ᵐ[q.atlasMeasure]
      (fun w => F₁ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradientFunction r w +
        F₂ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradientFunction u w) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨f,hf,hef⟩ := (C.scalar_lipschitzOn hL hr).extend_real
  obtain ⟨g,hg,heg⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (fun x => F (r x,u x))) (fun z => F (f z,g z)) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz]
    rw [←hef hz,←heg hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hf hef,
    ae_fderivWithin_eq_fderiv_extension volume C.borel hg heg,
    ae_fderivWithin_eq_fderiv_extension volume C.borel (hF.comp (hf.prodMk hg)) hecomp,
    hf.ae_differentiableAt.filter_mono ae_restrict_le,
    hg.ae_differentiableAt.filter_mono ae_restrict_le,ae_restrict_mem C.borel]
    with z hr' hu' hcomp hdf hdg hz
  change z ∈ C.domain at hz
  change q.normalizedCovector i (fun x => F (r x,u x)) z =
    F₁ (r (C.paramExtended z),u (C.paramExtended z)) • q.normalizedCovector i r z +
    F₂ (r (C.paramExtended z),u (C.paramExtended z)) • q.normalizedCovector i u z
  have hnf : f z = r (C.paramExtended z) := by
    rw [←hef hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hng : g z = u (C.paramExtended z) := by
    rw [←heg hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hd := (hdF (f z,g z)).comp z (hdf.hasFDerivAt.prodMk hdg.hasFDerivAt)
  rw [binaryDerivative_comp] at hd
  dsimp only [normalizedCovector,covector]
  rw [hcomp,hd.fderiv,hr',hu',hnf,hng]
  have he (a b : ℝ) (L M : Euc n →L[ℝ] ℝ) :
      differentialRow (a • L+b • M) = a • differentialRow L+b • differentialRow M := rfl
  rw [he,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,
    WithLp.toLp_add,WithLp.toLp_smul,WithLp.toLp_smul]

lemma gradient_bivariate_ae {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t) :
    q.gradient (hF.comp (hr.prodMk hu)) =ᵐ[q.atlasMeasure]
      (fun w => F₁ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradient hr w +
        F₂ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradient hu w) := by
  filter_upwards [(q.memLp_gradientFunction (hF.comp (hr.prodMk hu))).coeFn_toLp,
    (q.memLp_gradientFunction hr).coeFn_toLp,(q.memLp_gradientFunction hu).coeFn_toLp,
    q.gradientFunction_bivariate hr hu hF hdF] with w h1 h2 h3 h4
  change q.gradient (hF.comp (hr.prodMk hu)) w = _ at h1
  change q.gradient hr w = _ at h2
  change q.gradient hu w = _ at h3
  simp only [Function.comp_def] at h1
  rw [h1,h4,h2,h3]

end CAT0Fillings.ChartGeometry
end

end OAI
