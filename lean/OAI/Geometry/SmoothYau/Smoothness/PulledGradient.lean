import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsPreparationCovector
import OAI.Geometry.SmoothYau.Estimates.RadialSpeedPositiveAnnulus
import OAI.Geometry.SmoothYau.Geometry.MetricGradient
import OAI.Geometry.SmoothYau.Limits.CoordinateForm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def localMetricFlat (g : SmoothMetric E M) (p x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) (E →L[ℝ] ℝ)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) p x p x (g.inner x)

omit [FiniteDimensional ℝ E] in
lemma localMetricFlat_pairing (g : SmoothMetric E M) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) (v w : E) :
    localMetricFlat g p x v w = g.inner x
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x w) := by
  unfold localMetricFlat
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp

lemma localMetricFlat_invertible (g : SmoothMetric E M) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) :
    (localMetricFlat g p x).IsInvertible := by
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).continuousLinearEquivAt ℝ x hx
  have hi : Function.Injective (localMetricFlat g p x) := by
    apply (localMetricFlat g p x).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    by_contra hn
    have he : e.symm v ≠ 0 := by simpa only [ne_eq,EmbeddingLike.map_eq_zero_iff] using hn
    have hp := g.pos x (e.symm v) he
    have hz := congrArg (fun f : E →L[ℝ] ℝ => f v) hv
    change localMetricFlat g p x v v = 0 at hz
    rw [localMetricFlat_pairing g p x hx] at hz
    change g.inner x (e.symm v) (e.symm v) = 0 at hz
    linarith
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨(LinearEquiv.ofBijective (localMetricFlat g p x).toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,rfl⟩

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_localMetricFlat (g : SmoothMetric E M) (p : M) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (localMetricFlat g p) p := by
  have hg := g.contMDiff p
  rw [contMDiffAt_section p] at hg
  simp only [hom_trivializationAt_apply] at hg
  convert! hg using 1

lemma local_metricGradient (g : SmoothMetric E M) (u : M → ℝ) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,metricGradient g u x⟩).2 =
      (localMetricFlat g p x).inverse
        (inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,ℝ) id u
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u) p x) := by
  symm
  apply (localMetricFlat_invertible g p x hx).inverse_apply_eq.mpr
  ext w
  rw [localMetricFlat_pairing g p x hx,Trivialization.symm_apply_apply_mk _ hx,
    metricGradient_pairing]
  unfold inTangentCoordinates
  simp only [id_eq]
  have he := ContinuousLinearMap.inCoordinates_eq (ϕ := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x) hx
    (show u x ∈ (trivializationAt ℝ (TangentSpace 𝓘(ℝ,ℝ)) (u p)).baseSet by
      simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq])
  have hew := congrArg (fun L : E →L[ℝ] ℝ => L w) he
  exact hew.trans (by
    simp [Trivialization.continuousLinearEquivAt_apply,
      Trivialization.continuousLinearEquivAt_symm_apply]
    rfl)

theorem contMDiff_metricGradient (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun x => TotalSpace.mk' E x (metricGradient g u x)) := by
  intro p
  rw [contMDiffAt_section p]
  have hg := contMDiffAt_localMetricFlat g p
  have hi := (localMetricFlat_invertible g p p (mem_baseSet_trivializationAt E _ p)).contDiffAt_map_inverse (n := ∞)
  have hs := (hi.comp_contMDiffAt hg).clm_apply ((hu p).mfderiv_const (m := ∞) (by simp))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  exact local_metricGradient g u p x hx

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance metricDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance metricDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance metricFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def selfMetricFlat (g : SmoothMetric E E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner x).bilinearComp (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toContinuousLinearMap
    (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_apply (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = g.inner x v w := rfl

omit [FiniteDimensional ℝ E] in
lemma localMetricFlat_self (g : SmoothMetric E E) (p x : E) :
    localMetricFlat g p x = selfMetricFlat g x := by
  ext v w
  rw [localMetricFlat_pairing g p x (by simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq])]
  have hv (v : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v = v := by
    rw [←Trivialization.symmL_apply (R := ℝ) _ (by simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]) v,
      TangentBundle.symmL_model_space]
    rfl
  rw [hv,hv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma contDiff_selfMetricFlat (g : SmoothMetric E E) : ContDiff ℝ ∞ (selfMetricFlat g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := contMDiffAt_localMetricFlat g x
  rw [contMDiffAt_iff_contDiffAt] at h
  have heq : localMetricFlat g x = selfMetricFlat g := funext (localMetricFlat_self g x)
  rwa [heq] at h

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_symm (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = selfMetricFlat g x w v := g.symm x v w

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < selfMetricFlat g x v v := g.pos x v hv

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

def coordinateKoszul (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1/2 : ℝ) • (D+D.flip-(ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.comp D.flip)

lemma coordinateKoszul_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszul D v w z = (D v w z+D w v z-D z v w)/2 := by
  change (1/2 : ℝ) * (D v w z+D w v z-D z v w) = _
  ring

def metricChristoffel (g : SmoothMetric E E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) (selfMetricFlat g x).inverse).comp
    (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x))

lemma metricChristoffel_pairing (g : SmoothMetric E E) (x v w z : E) :
    selfMetricFlat g x (metricChristoffel g x v w) z =
      (fderiv ℝ (selfMetricFlat g) x v w z+fderiv ℝ (selfMetricFlat g) x w v z-
        fderiv ℝ (selfMetricFlat g) x z v w)/2 := by
  have h := (selfMetricFlat_invertible g x).inverse_apply_eq.mp
    (show (selfMetricFlat g x).inverse (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x) v w) =
      metricChristoffel g x v w from rfl)
  exact (congrArg (fun l : E →L[ℝ] ℝ => l z) h.symm).trans (coordinateKoszul_apply _ _ _ _)

lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

omit [FiniteDimensional ℝ E] in
lemma fderiv_selfMetricFlat_symm (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z = fderiv ℝ (selfMetricFlat g) x v z w := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  have he : (fun y => selfMetricFlat g y w z) = (fun y => selfMetricFlat g y z w) :=
    funext (fun y => selfMetricFlat_symm g y w z)
  have h := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  have heval (w z : E) : fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
    rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
        (differentiableAt_const z),
      fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  simpa only [heval] using h

lemma metricChristoffel_symm (g : SmoothMetric E E) (x v w : E) :
    metricChristoffel g x v w = metricChristoffel g x w v := by
  apply (selfMetricFlat_invertible g x).injective
  ext z
  rw [metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x z v w]
  ring

lemma metricChristoffel_compatible (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z =
      selfMetricFlat g x (metricChristoffel g x v w) z +
      selfMetricFlat g x w (metricChristoffel g x v z) := by
  rw [selfMetricFlat_symm g x w, metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x v z w]
  ring

lemma metricGradient_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g u x) =
      (selfMetricFlat g x).inverse (fderiv ℝ u x) := by
  symm
  apply (selfMetricFlat_invertible g x).inverse_apply_eq.mpr
  ext v
  have h := (metricGradient_pairing g u x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)).symm
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ u x v = g.inner x (metricGradient g u x) ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v) at h
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using h

theorem compact_positive_bilinear_lower {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ B x v v := by
  let S := K ×ˢ Metric.sphere (0:E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hc : Continuous (fun p : X × E => B p.1 p.2 p.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, ‖v‖ = 1 → m ≤ B x v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
      have hv : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
      refine ⟨B p.1 p.2 p.2,hpos p.1 hp.1 p.2 (norm_ne_zero_iff.mp (by rw [hv]; norm_num)),?_⟩
      intro x hx v hv
      exact hmin (show (x,v) ∈ S from ⟨hx,mem_sphere_zero_iff_norm.mpr hv⟩)
    · exact ⟨1,zero_lt_one,fun x hx v hv => (hne ⟨(x,v),hx,mem_sphere_zero_iff_norm.mpr hv⟩).elim⟩
  obtain ⟨m,hm,hmB⟩ := hm
  refine ⟨m,hm,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : B x v v = ‖v‖^2 * B x w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq,mul_comm m]
  exact mul_le_mul_of_nonneg_left (hmB x hx w hw) (sq_nonneg _)

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)

theorem compact_metric_tangent_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ J : ℝ, 0 < J ∧ ∀ x ∈ K, ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap‖ ≤ J := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹,inv_pos.mpr (Real.sqrt_pos.mpr hm),?_⟩
  intro x hx
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml x hx ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
  have hnorm : selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
      ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
    have hn := real_inner_self_eq_norm_sq (v : TangentSpace 𝓘(ℝ,E) x)
    change g.inner x v v = ‖v‖^2 at hn
    simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn
  rw [hnorm] at hlow
  have hh : Real.sqrt m * ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  change ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v‖ ≤ (Real.sqrt m)⁻¹ * ‖v‖
  rw [←div_eq_inv_mul,le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance genericHessMapNorm : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance genericHessMapSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance genericHessFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
def coordinateCovariantSecond (Γ : E → E →L[ℝ] E →L[ℝ] E) (f : E → V) (x : E) :
    E →L[ℝ] E →L[ℝ] V :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E V (fderiv ℝ f x)).comp (Γ x)

lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance actualDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance actualDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance actualFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance actualFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneStrict T q ↔ ∃ v, v ≠ 0 ∧ inner ℝ q v = 0 ∧ 0 < T v v := by
  constructor
  · rintro ⟨v,hv,hq,hp⟩
    exact ⟨v,norm_ne_zero_iff.mp (by rw [hv]; norm_num),hq,hp⟩
  · rintro ⟨v,hv,hq,hp⟩
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v,?_,?_,?_⟩
    · simp [norm_smul,ne_of_gt hn]
    · simp [inner_smul_right,hq]
    · simpa only [map_smul,smul_apply,smul_eq_mul] using
        mul_pos (inv_pos.mpr hn) (mul_pos (inv_pos.mpr hn) hp)

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneFull T q ↔ ∀ v, v ≠ 0 → inner ℝ q v = 0 → 0 < T v v := by
  constructor
  · intro h v hv hq
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hp := h (‖v‖⁻¹ • v)
      (by simp [norm_smul,ne_of_gt hn])
      (by simp [inner_smul_right,hq])
    simp only [map_smul,smul_apply,smul_eq_mul] at hp
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
      ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)
  · intro h v hv hq
    exact h v (norm_ne_zero_iff.mp (by rw [hv]; norm_num)) hq

def actualCoordinateHessian (g : SmoothMetric E E) (u : E → ℝ) : E → CoordinateForm E :=
  coordinateCovariantSecond (metricChristoffel g) u

def coordinateMetricGradient (g : SmoothMetric E E) (ψ : E → ℝ) (x : E) : E :=
  (selfMetricFlat g x).inverse (fderiv ℝ ψ x)

lemma coordinateMetricGradient_eq (g : SmoothMetric E E) (ψ : E → ℝ) (x : E) :
    coordinateMetricGradient g ψ x =
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g ψ x) :=
  (metricGradient_self g ψ x).symm

lemma contDiff_coordinateMetricGradient (g : SmoothMetric E E) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (coordinateMetricGradient g ψ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  exact hGi.clm_apply (hψ.fderiv_right (m:=∞) (by simp))

def actualProfileTraceForm (g : SmoothMetric E E) (u : E → ℝ) (x : E) : CoordinateForm E :=
  metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x)
    (coordinateMetricGradient g u x)

def actualProfileStrict (g : SmoothMetric E E) (u : E → ℝ) (x : E) : Prop :=
  quadraticPlaneStrict (actualProfileTraceForm g u x)
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))

def actualProfileFull (g : SmoothMetric E E) (u : E → ℝ) (x : E) : Prop :=
  quadraticPlaneFull (actualProfileTraceForm g u x)
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))

lemma continuous_actualProfileTraceForm (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileTraceForm g u) :=
  by
    have hB : Continuous (selfMetricFlat g) := (contDiff_selfMetricFlat g).continuous
    have hH : Continuous (actualCoordinateHessian g u) :=
      continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu
    have ha : Continuous (coordinateMetricGradient g u) :=
      (contDiff_coordinateMetricGradient g hu).continuous
    change Continuous (fun x => metricProfileTraceForm (selfMetricFlat g x)
      (actualCoordinateHessian g u x) (coordinateMetricGradient g u x))
    unfold metricProfileTraceForm
    exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
      ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_metric_norm (g : SmoothMetric E E) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v : TangentSpace 𝓘(ℝ,E) x,
      selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
        ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro v
  have hn := real_inner_self_eq_norm_sq v
  change g.inner x v v = ‖v‖^2 at hn
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn

lemma actualProfileTraceForm_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    let H := (actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
    ∀ v : TangentSpace 𝓘(ℝ,E) x, actualProfileTraceForm g u x (j v) (j v) =
      ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
        (1+‖metricGradient g u x‖^2)*H v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j H v
  rw [actualProfileTraceForm,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
  rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
  rfl

omit [FiniteDimensional ℝ E] in
lemma profileStrict_iff_quadratic (H : ProfileForm E) (a : E) :
    profileStrict H a ↔ quadraticPlaneStrict (metricProfileTraceForm (innerSL ℝ) H a) a := by
  have ht (v : E) (hv : ‖v‖ = 1) :
      metricProfileTraceForm (innerSL ℝ) H a v v = profileTrace H a v := by
    rw [metricProfileTraceForm_apply]
    change inner ℝ v v * H a a + (1+inner ℝ a a)*H v v = profileTrace H a v
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,one_mul,profileTrace]
  constructor
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv]⟩
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv] at hp⟩

omit [FiniteDimensional ℝ E] in
lemma profileFull_iff_quadratic (H : ProfileForm E) (a : E) :
    profileFull H a ↔ quadraticPlaneFull (metricProfileTraceForm (innerSL ℝ) H a) a := by
  have ht (v : E) (hv : ‖v‖ = 1) :
      metricProfileTraceForm (innerSL ℝ) H a v v = profileTrace H a v := by
    rw [metricProfileTraceForm_apply]
    change inner ℝ v v * H a a + (1+inner ℝ a a)*H v v = profileTrace H a v
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,one_mul,profileTrace]
  constructor <;> intro h v hv hav
  · rw [ht v hv]
    exact h v hv hav
  · rw [←ht v hv]
    exact h v hv hav

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_transport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (j : V ≃L[ℝ] E) (T : CoordinateForm E) (S : CoordinateForm V)
    (q : E) (a : V) (hT : ∀ v, T (j v) (j v) = S v v)
    (hq : ∀ v, inner ℝ q (j v) = inner ℝ a v) :
    quadraticPlaneStrict T q ↔ quadraticPlaneStrict S a := by
  rw [quadraticPlaneStrict_iff_nonzero,quadraticPlaneStrict_iff_nonzero]
  constructor
  · rintro ⟨v,hv,hqv,hp⟩
    refine ⟨j.symm v,by simpa using hv,?_,?_⟩
    · rw [←hq,j.apply_symm_apply]
      exact hqv
    · rwa [←hT,j.apply_symm_apply]
  · rintro ⟨v,hv,hqv,hp⟩
    exact ⟨j v,by simpa using hv,(hq v).trans hqv,by rwa [hT]⟩

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_transport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (j : V ≃L[ℝ] E) (T : CoordinateForm E) (S : CoordinateForm V)
    (q : E) (a : V) (hT : ∀ v, T (j v) (j v) = S v v)
    (hq : ∀ v, inner ℝ q (j v) = inner ℝ a v) :
    quadraticPlaneFull T q ↔ quadraticPlaneFull S a := by
  rw [quadraticPlaneFull_iff_nonzero,quadraticPlaneFull_iff_nonzero]
  constructor
  · intro h v hv hqv
    rw [←hT]
    exact h (j v) (by simpa using hv) ((hq v).trans hqv)
  · intro h v hv hqv
    have horth : inner ℝ a (j.symm v) = 0 := by
      rw [←hq,j.apply_symm_apply]
      exact hqv
    have hp := h (j.symm v) (by simpa using hv) horth
    simpa only [←hT,j.apply_symm_apply] using hp

lemma coordinateProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (H₀ : CoordinateForm E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    quadraticPlaneStrict (metricProfileTraceForm (selfMetricFlat g x) H₀ (coordinateMetricGradient g u x))
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ↔ profileStrict
      (H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  rw [profileStrict_iff_quadratic]
  apply quadraticPlaneStrict_transport j
  · intro v
    rw [metricProfileTraceForm_apply,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
    rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
    change ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
      (1+‖metricGradient g u x‖^2)*H v v =
      inner ℝ v v*H (metricGradient g u x) (metricGradient g u x) +
      (1+inner ℝ (metricGradient g u x) (metricGradient g u x))*H v v
    simp only [real_inner_self_eq_norm_sq]
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    change fderiv ℝ u x (j v) = g.inner x (metricGradient g u x) v
    rw [metricGradient_pairing,mfderiv_eq_fderiv]
    rfl

lemma coordinateProfileFull_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (H₀ : CoordinateForm E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    quadraticPlaneFull (metricProfileTraceForm (selfMetricFlat g x) H₀ (coordinateMetricGradient g u x))
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ↔ profileFull
      (H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  rw [profileFull_iff_quadratic]
  apply quadraticPlaneFull_transport j
  · intro v
    rw [metricProfileTraceForm_apply,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
    rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
    change ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
      (1+‖metricGradient g u x‖^2)*H v v =
      inner ℝ v v*H (metricGradient g u x) (metricGradient g u x) +
      (1+inner ℝ (metricGradient g u x) (metricGradient g u x))*H v v
    simp only [real_inner_self_eq_norm_sq]
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    change fderiv ℝ u x (j v) = g.inner x (metricGradient g u x) v
    rw [metricGradient_pairing,mfderiv_eq_fderiv]
    rfl

lemma actualProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    actualProfileStrict g u x ↔ profileStrict
      ((actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) :=
  coordinateProfileStrict_iff_tangent g u x (actualCoordinateHessian g u x)

lemma actualProfileFull_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    actualProfileFull g u x ↔ profileFull
      ((actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) :=
  coordinateProfileFull_iff_tangent g u x (actualCoordinateHessian g u x)

theorem exists_actual_preparation_covector (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) (hs : actualProfileStrict g u x) :
    ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ l (coordinateMetricGradient g u x) = 0 ∧
      (∀ c : ℝ, quadraticPlaneStrict
        (metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x+c • profileRankOne l)
          (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
      ∃ C : ℕ, ∀ c : ℝ, C ≤ c → quadraticPlaneFull
        (metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x+c • profileRankOne l)
          (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := (actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,E) x) = 3 :=
    j.toLinearEquiv.finrank_eq.trans hd
  have ha' : metricGradient g u x ≠ 0 := by
    intro h
    apply ha
    rw [coordinateMetricGradient_eq,h,map_zero]
  obtain ⟨l,hl,hla,hlS,C,hlF⟩ := exists_preparation_covector hdim ha'
    ((actualProfileStrict_iff_tangent g u x).mp hs)
  let l₀ := l.comp j.symm.toContinuousLinearMap
  have hform (c : ℝ) :
      (actualCoordinateHessian g u x+c • profileRankOne l₀).bilinearComp
        j.toContinuousLinearMap j.toContinuousLinearMap = H+c • profileRankOne l := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,add_apply,
      smul_apply,profileRankOne,ContinuousLinearMap.smulRight_apply,
      l₀,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul,H]
  refine ⟨l₀,?_,?_,?_,C,?_⟩
  · intro h
    apply hl
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (j v)) h
    simpa only [l₀,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply,zero_apply] using hh
  · rw [coordinateMetricGradient_eq]
    simpa only [l₀,j,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hla
  · intro c
    apply (coordinateProfileStrict_iff_tangent g u x _).mpr
    rw [hform]
    exact hlS c
  · intro c hc
    apply (coordinateProfileFull_iff_tangent g u x _).mpr
    rw [hform]
    exact hlF c hc


end

section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma second_directional_eq {f : E → V} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ f z w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply
    ((hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

lemma smooth_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (F ∘ y) z w) x v =
      fderiv ℝ (fderiv ℝ F) (y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      fderiv ℝ F (y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hdF := hF.differentiable (by simp)
  have hdy := hy.differentiable (by simp)
  have hdDF := (hF.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hdDy := (hy.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (F ∘ y) z w) =
      (fun z => fderiv ℝ F (y z) (fderiv ℝ y z w)) := by
    funext z
    rw [fderiv_comp z (hdF _) (hdy _),ContinuousLinearMap.comp_apply]
  rw [he]
  erw [fderiv_clm_apply ((hdDF _).comp x (hdy _))
    ((hdDy x).clm_apply (differentiableAt_const w))]
  erw [fderiv_fun_comp x (hdDF _) (hdy _)]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma smooth_product_second {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t*g t) z w) x v =
      f x * fderiv ℝ (fun z => fderiv ℝ g z w) x v +
      fderiv ℝ f x v * fderiv ℝ g x w +
      fderiv ℝ f x w * fderiv ℝ g x v +
      g x * fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t*g t) z w) =
      (fun z => f z * fderiv ℝ g z w + g z * fderiv ℝ f z w) := by
    funext z
    rw [fderiv_fun_mul (df z) (dg z)]
    simp
  rw [he]
  erw [fderiv_fun_add ((df x).mul ((dDg x).clm_apply (differentiableAt_const w)))
    ((dg x).mul ((dDf x).clm_apply (differentiableAt_const w))),
    fderiv_fun_mul (df x) ((dDg x).clm_apply (differentiableAt_const w)),
    fderiv_fun_mul (dg x) ((dDf x).clm_apply (differentiableAt_const w))]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

theorem corrugation_first {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v : E) :
    fderiv ℝ (fun z => ψ z+c*χ z*F (N • y z)) x v =
      fderiv ℝ ψ x v + c*fderiv ℝ χ x v*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v) := by
  have dhψ := hψ.differentiable (by simp) x
  have dhχ := hχ.differentiable (by simp) x
  have dhy := hy.differentiable (by simp) x
  have dhF := hF.differentiable (by simp) (N • y x)
  have dhny := dhy.const_smul N
  have dhcomp := dhF.comp x dhny
  erw [fderiv_fun_add dhψ ((dhχ.const_mul c).mul dhcomp),
    fderiv_fun_mul (dhχ.const_mul c) dhcomp,
    fderiv_const_mul dhχ c, fderiv_fun_comp x dhF dhny,
    fderiv_fun_const_smul dhy N]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_smul,smul_eq_mul,Function.comp_apply,Pi.smul_apply]
  ring


end

section
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma smooth_sum_second {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t+g t) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v +
      fderiv ℝ (fun z => fderiv ℝ g z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t+g t) z w) =
      (fun z => fderiv ℝ f z w + fderiv ℝ g z w) := by
    funext z; rw [fderiv_fun_add (df z) (dg z)]; rfl
  rw [he, fderiv_fun_add ((dDf x).clm_apply (differentiableAt_const w))
    ((dDg x).clm_apply (differentiableAt_const w))]
  rfl
lemma smooth_const_smul_second {f : E → V}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => c • f t) z w) x v =
      c • fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => c • f t) z w) =
      (fun z => c • fderiv ℝ f z w) := by
    funext z; rw [fderiv_fun_const_smul (df z) c]; rfl
  rw [he, fderiv_fun_const_smul ((dDf x).clm_apply (differentiableAt_const w)) c]
  rfl

lemma scaled_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v =
      N^2 * fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      N * fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hh := smooth_comp_second hF (hy.const_smul N) x v w
  change fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v = _ at hh
  rw [fderiv_fun_const_smul (hy.differentiable (by simp) x) N,
    smooth_const_smul_second hy N x v w] at hh
  simp only [_root_.smul_apply,map_smul,smul_eq_mul] at hh
  rw [hh]
  ring

theorem corrugation_second {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => ψ t+c*(χ t*F (N • y t))) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ ψ z w) x v +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*fderiv ℝ (fun z => fderiv ℝ χ z w) x v := by
  have hg : ContDiff ℝ ∞ (fun t => F (N • y t)) := hF.comp (hy.const_smul N)
  have hh := smooth_sum_second hψ ((hχ.mul hg).const_smul c) x v w
  simp only [smul_eq_mul] at hh
  rw [hh]
  have hc := smooth_const_smul_second (hχ.mul hg) c x v w
  simp only [smul_eq_mul] at hc
  rw [hc,smooth_product_second hχ hg x v w,scaled_comp_second hF hy N x v w]
  have hfirst (z : E) : fderiv ℝ (fun t => F (N • y t)) x z =
      N * fderiv ℝ F (N • y x) (fderiv ℝ y x z) := by
    erw [fderiv_fun_comp x (hF.differentiable (by simp) _) ((hy.differentiable (by simp) x).const_smul N),
      fderiv_fun_const_smul (hy.differentiable (by simp) x) N]
    simp
  rw [hfirst w,hfirst v]
  ring

end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma periodicRadialOffset_norm_le {R : ℝ} (hR : 0 ≤ R) (x : ProfilePlane) :
    ‖periodicRadialOffset R x‖ ≤ R := by
  classical
  unfold periodicRadialOffset
  split_ifs with h
  · exact h.choose_spec.le
  · simpa using hR

lemma periodicRadialOffset_radius_sq_le {R : ℝ} (hR : 0 ≤ R) (x : ProfilePlane) :
    (periodicRadialOffset R x).1^2+(periodicRadialOffset R x).2^2 ≤ 2*R^2 := by
  have hn := periodicRadialOffset_norm_le hR x
  have h1 := (norm_fst_le (periodicRadialOffset R x)).trans hn
  have h2 := (norm_snd_le (periodicRadialOffset R x)).trans hn
  rw [Real.norm_eq_abs] at h1 h2
  have hsq1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsq2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  simpa only [sq_abs] using (show
    |(periodicRadialOffset R x).1|^2+|(periodicRadialOffset R x).2|^2 ≤ 2*R^2 by
      linarith only [hsq1,hsq2])

theorem periodicRadial_coefficients_bounded {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβv : ∀ t, β t ∈ Icc 0 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ M S K : ℝ, 0 < M ∧ 0 < S ∧ 0 < K ∧ ∀ x : ProfilePlane,
      0 ≤ periodicRadialSpeed β R x ∧ periodicRadialSpeed β R x ≤ M ∧
      0 ≤ periodicAngularSecond β R x ∧
      (periodicRadialSpeed β R x)^2 ≤ S*periodicAngularSecond β R x ∧
      |periodicRadialSecond β R x| ≤ K := by
  obtain ⟨D,hD⟩ := (hβc.deriv.isCompact_range (hβ.continuous_deriv (by simp))).exists_bound_of_continuousOn
    (f := id) continuous_id.continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  have hDb : ∀ t, |deriv β t| ≤ D' := fun t =>
    (hD _ (mem_range_self t)).trans (le_max_left _ _)
  refine ⟨4*R+1,4*R^2+1,3+8*R^2*D',by positivity,by positivity,by positivity,?_⟩
  intro x
  let z := periodicRadialOffset R x
  let t := z.1^2+z.2^2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htb : t ≤ 2*R^2 := periodicRadialOffset_radius_sq_le hR.le x
  have hs : (Real.sqrt t)^2 = t := Real.sq_sqrt ht
  have hsp : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsb : Real.sqrt t ≤ 2*R := by nlinarith only [hs,hsp,htb,hR]
  have hp := (hβv t).1
  have hb := (hβv t).2
  have hbp : 0 ≤ β t*(1-β t) := mul_nonneg hp (sub_nonneg.mpr hb)
  change 0 ≤ 2*Real.sqrt t*β t ∧ 2*Real.sqrt t*β t ≤ 4*R+1 ∧
    0 ≤ 2*β t ∧ (2*Real.sqrt t*β t)^2 ≤ (4*R^2+1)*(2*β t) ∧
    |2*β t+4*t*deriv β t| ≤ 3+8*R^2*D'
  refine ⟨by positivity,?_,by positivity,?_,?_⟩
  · have hh := mul_le_mul hsb hb hp (by positivity : 0 ≤ 2*R)
    nlinarith only [hh]
  · calc
      (2*Real.sqrt t*β t)^2 = 4*t*(β t)^2 := by rw [mul_pow,mul_pow,hs]; ring
      _ ≤ 4*t*β t := mul_le_mul_of_nonneg_left (by nlinarith only [hbp]) (by positivity)
      _ ≤ 8*R^2*β t := by nlinarith only [mul_le_mul_of_nonneg_right htb hp]
      _ ≤ (4*R^2+1)*(2*β t) := by nlinarith only [hp]
  · calc
      |2*β t+4*t*deriv β t| ≤ |2*β t|+|4*t*deriv β t| := abs_add_le _ _
      _ = 2*β t+4*t*|deriv β t| := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2*β t),abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*t)]
      _ ≤ 2+4*(2*R^2)*D' := add_le_add (by linarith only [hb])
        (mul_le_mul (by nlinarith only [htb]) (hDb t) (abs_nonneg _) (by positivity))
      _ ≤ 3+8*R^2*D' := by ring_nf; linarith

theorem periodicRadialFunction_bounded {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, |periodicRadialFunction β b x| ≤ B := by
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 := fun z hz => hf z (hrR.trans hz)
  obtain ⟨B,hB⟩ := ((radialSquaredBase_compact hβ.continuous hr hb hzero).isCompact_range
    (radialSquaredBase_smooth β b hβ).continuous).exists_bound_of_continuousOn
    (f := id) continuous_id.continuousOn
  refine ⟨|radialPrimitive β b|+max B 0+1,by positivity,?_⟩
  intro x
  have hp : |profilePeriodize (radialSquaredBase β b) x| ≤ max B 0 := by
    by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
    · rw [(profilePeriodize_eventually_single hsmall hfR hx.choose hx.choose_spec).eq_of_nhds]
      exact (hB _ (mem_range_self _)).trans (le_max_left _ _)
    · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
      rw [(profilePeriodize_eventually_zero hrR hf x hxn).eq_of_nhds]
      simp
  unfold periodicRadialFunction
  calc
    _ ≤ |radialPrimitive β b|+|profilePeriodize (radialSquaredBase β b) x| := abs_add_le _ _
    _ ≤ |radialPrimitive β b|+max B 0+1 := by linarith only [hp]

theorem periodicRadialFunction_fderiv_bound {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβp : ∀ t, 0 ≤ β t)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) (x : ProfilePlane) :
    ‖fderiv ℝ (periodicRadialFunction β b) x‖ ≤ 2*periodicRadialSpeed β R x := by
  have he : fderiv ℝ (periodicRadialFunction β b) x =
      periodicRadialSpeed β R x • planeRadialCovector (periodicRadialOffset R x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact periodicRadialFunction_first hβ hβ0 hr hrR hsmall hb hzero x v
  have hp : 0 ≤ periodicRadialSpeed β R x := by
    unfold periodicRadialSpeed
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (hβp _)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]
  nlinarith only [mul_le_mul_of_nonneg_left (norm_planeRadialCovector_le (periodicRadialOffset R x)) hp]


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def pulledGradient (j : V →L[ℝ] E) (u : E → ℝ) (x : E) : V :=
  (InnerProductSpace.toDual ℝ V).symm ((fderiv ℝ u x).comp j)

omit [FiniteDimensional ℝ E] in
lemma pulledGradient_pairing (j : V →L[ℝ] E) (u : E → ℝ) (x : E) (v : V) :
    inner ℝ (pulledGradient j u x) v = fderiv ℝ u x (j v) :=
  InnerProductSpace.toDual_symm_apply

def pulledHessian (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (u : E → ℝ) (x : E) : ProfileForm V :=
  (coordinateCovariantSecond Γ u x).bilinearComp j j

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma norm_bilinear_pullback_le (H : ProfileForm E) (j : V →L[ℝ] E) :
    ‖H.bilinearComp j j‖ ≤ ‖H‖*‖j‖^2 := by
  apply (H.bilinearComp j j).opNorm_le_bound₂ (by positivity)
  intro v w
  calc
    ‖H (j v) (j w)‖ ≤ ‖H‖*‖j v‖*‖j w‖ := H.le_opNorm₂ _ _
    _ ≤ ‖H‖*(‖j‖*‖v‖)*(‖j‖*‖w‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (j.le_opNorm v) (norm_nonneg H))
        (j.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma planeRadialCovector_le_radius (z v : ProfilePlane) :
    |planeRadialCovector z v| ≤ Real.sqrt (v.1^2+v.2^2) := by
  have he := plane_radial_angular_sq z v
  have hs := Real.sq_sqrt (show 0 ≤ v.1^2+v.2^2 by positivity)
  have ha := sq_abs (planeRadialCovector z v)
  nlinarith only [he,hs,ha,sq_nonneg (planeAngularCovector z v),
    abs_nonneg (planeRadialCovector z v),Real.sqrt_nonneg (v.1^2+v.2^2)]

lemma radial_coframe_bounds (D : V →L[ℝ] ProfilePlane) (a : V) (z : ProfilePlane)
    (ha : D a = 0)
    (hup : ∀ v, Real.sqrt ((D v).1^2+(D v).2^2) ≤ 2*‖v‖)
    (hlo : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((D v).1^2+(D v).2^2)) :
    let R := (planeRadialCovector z).comp D
    let T := (planeAngularCovector z).comp D
    R a = 0 ∧ T a = 0 ∧ ‖(InnerProductSpace.toDual ℝ V).symm R‖ ≤ 2 ∧
      ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2) := by
  dsimp only
  refine ⟨by simp [ha],by simp [ha],?_,?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (planeRadialCovector_le_radius z (D v)).trans (hup v)
  · intro v hv
    simpa only [ContinuousLinearMap.comp_apply,plane_radial_angular_sq] using hlo v hv

lemma periodicRadialSpeed_le_angular {β : ℝ → ℝ} (hβ : ∀ t, 0 ≤ β t)
    {R : ℝ} (hR : 0 < R) (x : ProfilePlane) :
    periodicRadialSpeed β R x/(2*R) ≤ periodicAngularSecond β R x := by
  let z := periodicRadialOffset R x
  let t := z.1^2+z.2^2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htb : t ≤ 2*R^2 := periodicRadialOffset_radius_sq_le hR.le x
  have hs : Real.sqrt t ≤ 2*R := by
    nlinarith only [Real.sq_sqrt ht,Real.sqrt_nonneg t,htb,hR]
  apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
  change 2*Real.sqrt t*β t ≤ (2*β t)*(2*R)
  nlinarith only [mul_le_mul_of_nonneg_right hs (hβ t)]

def radialCorrugation (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ)
    (b δ A N : ℝ) (x : E) : ℝ :=
  ψ x+(δ*A/N)*(χ x*periodicRadialFunction β b (N • y x))

omit [FiniteDimensional ℝ E] in
lemma radialCorrugation_smooth {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b r R : ℝ} (hr : 0 ≤ r)
    (_hrR : r < R) (_hsmall : 2*R < 1) (hb : b ≤ r^2)
    (hzero : ∀ t, b ≤ t → β t = 0) (δ A N : ℝ) :
    ContDiff ℝ ∞ (radialCorrugation ψ χ y β b δ A N) := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) := by
    exact radial_periodic_smooth hβ hr hb hzero
  exact hψ.add (contDiff_const.mul (hχ.mul (hF.comp (hy.const_smul N))))

omit [FiniteDimensional ℝ E] in
lemma radialCorrugation_gradient {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (j : V →L[ℝ] E) (δ A N : ℝ) (hN : N ≠ 0) (x : E) :
    pulledGradient j (radialCorrugation ψ χ y β b δ A N) x =
      pulledGradient j ψ x +
        (δ*A*χ x*periodicRadialSpeed β R (N • y x)) •
          (InnerProductSpace.toDual ℝ V).symm
            ((planeRadialCovector (periodicRadialOffset R (N • y x))).comp ((fderiv ℝ y x).comp j)) +
        (δ*A/N*periodicRadialFunction β b (N • y x)) • pulledGradient j χ x := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) :=
    radial_periodic_smooth hβ hr hb hzero
  apply ext_inner_right ℝ
  intro v
  rw [pulledGradient_pairing,inner_add_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    pulledGradient_pairing,pulledGradient_pairing,InnerProductSpace.toDual_symm_apply]
  have he := corrugation_first hψ hχ hF hy (δ*A/N) N x (j v)
  have heq : (fun z => ψ z+(δ*A/N)*χ z*periodicRadialFunction β b (N • y z)) =
      radialCorrugation ψ χ y β b δ A N := by funext z; dsimp [radialCorrugation]; ring
  rw [heq,periodicRadialFunction_first hβ hβ0 hr hrR hsmall hb hzero] at he
  simp only [ContinuousLinearMap.comp_apply]
  rw [he]
  field_simp [hN]
  ring



end YauCounterexamples
end

end OAI
