import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance normalDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance normalDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance normalFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalTriNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalTriSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma exists_metric_orthonormal_frame (g : SmoothMetric E E) (p : E) :
    ∃ A : E ≃L[ℝ] E, ∀ v w, selfMetricFlat g p (A v) (A w) = inner ℝ v w := by
  let : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) p
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) :=
    Module.Finite.equiv j.symm.toLinearEquiv
  let e : E ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ,E) p :=
    (stdOrthonormalBasis ℝ E).equiv
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ,E) p))
      (finCongr j.toLinearEquiv.finrank_eq.symm)
  refine ⟨e.toContinuousLinearEquiv.trans j, ?_⟩
  intro v w
  have h := e.inner_map_map v w
  change g.inner p (e v) (e w) = inner ℝ v w at h
  simpa only [selfMetricFlat, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    j] using h

def normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) (x : E) : E :=
  p + A x - (1 / 2 : ℝ) • C x x

omit [FiniteDimensional ℝ E] in
lemma contDiff_normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (normalJetMap p A C) :=
  (contDiff_const.add A.contDiff).sub ((C.contDiff.clm_apply contDiff_id).const_smul (1/2 : ℝ))

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_zero (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    normalJetMap p A C 0 = p := by simp [normalJetMap]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    HasFDerivAt (normalJetMap p A C) (A - C x) x := by
  have h := ((hasFDerivAt_const p x).add A.hasFDerivAt).sub
    ((C.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1/2 : ℝ))
  change HasFDerivAt (fun y => p + A y - (1/2 : ℝ) • C y y) (A - C x) x
  apply h.congr_fderiv
  ext v
  simp only [_root_.sub_apply, _root_.add_apply,
    zero_add, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, id_eq, hC v x, ← two_smul ℝ, smul_smul]
  norm_num

omit [FiniteDimensional ℝ E] in
lemma fderiv_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    fderiv ℝ (normalJetMap p A C) x = A - C x :=
  (hasFDerivAt_normalJetMap p A C hC x).fderiv

lemma normalJetMap_local_diffeomorphism (p : E) (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = normalJetMap p A C ∧
      0 ∈ e.source ∧ p ∈ e.target ∧ ContDiffAt ℝ ∞ (e.symm : E → E) p := by
  have hf := (contDiff_normalJetMap p A C).contDiffAt (x := (0 : E))
  have hd : HasFDerivAt (normalJetMap p A C) (A : E →L[ℝ] E) 0 := by
    simpa only [map_zero, sub_zero] using hasFDerivAt_normalJetMap p A C hC 0
  let e := hf.toOpenPartialHomeomorph (normalJetMap p A C) hd (by simp)
  refine ⟨e, rfl, hf.mem_toOpenPartialHomeomorph_source hd (by simp), ?_, ?_⟩
  · simpa only [normalJetMap_zero] using hf.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  · change ContDiffAt ℝ ∞ (hf.localInverse hd (by simp)) p
    have hi := hf.to_localInverse hd (by simp)
    simpa only [normalJetMap_zero] using hi

def normalMetricTensor (g : SmoothMetric E E) (p : E) (A : E →L[ℝ] E)
    (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let C := (metricChristoffel g p).bilinearComp A A
  (selfMetricFlat g (normalJetMap p A C x)).bilinearComp (A - C x) (A - C x)

lemma normalMetricTensor_is_pullback (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (x v w : E) :
    normalMetricTensor g p A x v w = selfMetricFlat g
      (normalJetMap p A ((metricChristoffel g p).bilinearComp A A) x)
      (fderiv ℝ (normalJetMap p A ((metricChristoffel g p).bilinearComp A A)) x v)
      (fderiv ℝ (normalJetMap p A ((metricChristoffel g p).bilinearComp A A)) x w) := by
  rw [fderiv_normalJetMap p A _ (fun v w => metricChristoffel_symm g p (A v) (A w))]
  rfl

lemma normalMetricTensor_at_zero (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) :
    normalMetricTensor g p A 0 = (selfMetricFlat g p).bilinearComp A A := by
  simp [normalMetricTensor, normalJetMap_zero]

lemma contDiff_normalMetricTensor_apply (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (v w : E) :
    ContDiff ℝ ∞ (fun x => normalMetricTensor g p A x v w) := by
  let C := (metricChristoffel g p).bilinearComp A A
  have hF := contDiff_normalJetMap p A C
  have hV (v : E) : ContDiff ℝ ∞ (fun x => (A - C x) v) :=
    (contDiff_const.sub C.contDiff).clm_apply contDiff_const
  exact (((contDiff_selfMetricFlat g).comp hF).clm_apply (hV v)).clm_apply (hV w)

lemma normalMetricTensor_normal_jet (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (v w : E) :
    fderiv ℝ (fun x => normalMetricTensor g p A x v w) 0 = 0 := by
  let C := (metricChristoffel g p).bilinearComp A A
  have hC : ∀ v w, C v w = C w v := fun v w => metricChristoffel_symm g p (A v) (A w)
  have hF : HasFDerivAt (normalJetMap p A C) A 0 := by
    simpa only [map_zero, sub_zero] using hasFDerivAt_normalJetMap p A C hC 0
  have hB := ((contDiff_selfMetricFlat g).differentiable (by simp) p).hasFDerivAt
  have hV (v : E) : HasFDerivAt (fun x => (A - C x) v) (-(C.flip v)) 0 := by
    have hh := (hasFDerivAt_const (A v) (0 : E)).sub (C.flip v).hasFDerivAt
    have hh' := hh.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun x => show (A - C x) v = ((fun _ : E => A v) - (C.flip v : E → E)) x by rfl))
    simpa only [zero_sub] using hh'
  have hBF : HasFDerivAt (fun x => selfMetricFlat g (normalJetMap p A C x))
      ((fderiv ℝ (selfMetricFlat g) p).comp A) 0 := by
    have hB' : HasFDerivAt (selfMetricFlat g) (fderiv ℝ (selfMetricFlat g) p)
        (normalJetMap p A C 0) := by rw [normalJetMap_zero]; exact hB
    exact hB'.comp 0 hF
  have hD := (hBF.clm_apply (hV v)).clm_apply (hV w)
  have hz : HasFDerivAt (fun x => normalMetricTensor g p A x v w) (0 : E →L[ℝ] ℝ) 0 := by
    change HasFDerivAt (fun y => selfMetricFlat g (normalJetMap p A C y)
      ((A - C y) v) ((A - C y) w)) (0 : E →L[ℝ] ℝ) 0
    apply hD.congr_fderiv
    ext u
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, _root_.neg_apply, map_neg,
      normalJetMap_zero, map_zero, sub_zero, _root_.zero_apply]
    change -selfMetricFlat g p (A v) (C u w) +
      (-selfMetricFlat g p (C u v) (A w) +
        fderiv ℝ (selfMetricFlat g) p (A u) (A v) (A w)) = 0
    rw [metricChristoffel_compatible]
    dsimp only [C, ContinuousLinearMap.bilinearComp_apply]
    ring
  exact hz.fderiv

theorem exists_smooth_normal_coordinate_jet (g : SmoothMetric E E) (p : E) :
    ∃ A : E ≃L[ℝ] E, ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = normalJetMap p A ((metricChristoffel g p).bilinearComp A.toContinuousLinearMap A.toContinuousLinearMap) ∧
      0 ∈ e.source ∧ p ∈ e.target ∧ ContDiffAt ℝ ∞ (e.symm : E → E) p ∧
      (∀ v w, normalMetricTensor g p A 0 v w = inner ℝ v w) ∧
      (∀ v w, fderiv ℝ (fun x => normalMetricTensor g p A x v w) 0 = 0) := by
  obtain ⟨A, hA⟩ := exists_metric_orthonormal_frame g p
  obtain ⟨e, he, h0, hp, hi⟩ := normalJetMap_local_diffeomorphism p A
    ((metricChristoffel g p).bilinearComp A.toContinuousLinearMap A.toContinuousLinearMap)
    (fun v w => metricChristoffel_symm g p (A v) (A w))
  refine ⟨A, e, he, h0, hp, hi, ?_, normalMetricTensor_normal_jet g p A⟩
  intro v w
  rw [normalMetricTensor_at_zero]
  exact hA v w


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_remainder (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    normalJetMap p A C x - normalJetMap p A C y - A (x-y) =
      -(1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
  simp only [normalJetMap, map_sub, _root_.sub_apply, smul_add, smul_sub]
  module

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_approximates (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (r : ℝ≥0) :
    ApproximatesLinearOn (normalJetMap p A C) A (Metric.ball 0 r) (‖C‖₊ * r) := by
  intro x hx y hy
  rw [normalJetMap_remainder, norm_smul, Real.norm_eq_abs]
  have hhalf : |-(1/2:ℝ)|=(1/2:ℝ) := by norm_num
  rw [hhalf]
  change (1/2:ℝ) * ‖C x (x-y) + C (x-y) y‖ ≤ (‖C‖*(r:ℝ))*‖x-y‖
  have hx' : ‖x‖ ≤ (r : ℝ) := (mem_ball_zero_iff.mp hx).le
  have hy' : ‖y‖ ≤ (r : ℝ) := (mem_ball_zero_iff.mp hy).le
  have h1 : ‖C x (x-y)‖ ≤ ‖C‖ * (r : ℝ) * ‖x-y‖ := by
    calc
      _ ≤ ‖C x‖ * ‖x-y‖ := (C x).le_opNorm _
      _ ≤ (‖C‖ * ‖x‖) * ‖x-y‖ := mul_le_mul_of_nonneg_right (C.le_opNorm x) (norm_nonneg _)
      _ ≤ _ := by gcongr
  have h2 : ‖C (x-y) y‖ ≤ ‖C‖ * (r : ℝ) * ‖x-y‖ := by
    calc
      _ ≤ ‖C (x-y)‖ * ‖y‖ := (C (x-y)).le_opNorm _
      _ ≤ (‖C‖ * ‖x-y‖) * ‖y‖ := mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖C‖ * ‖x-y‖) * r := by gcongr
      _ = _ := by ring
  have hs := norm_add_le (C x (x-y)) (C (x-y) y)
  linarith

lemma normalJetMap_derivative_invertible (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) {x : E}
    (hx : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1) :
    (A.toContinuousLinearMap - C x).IsInvertible := by
  have hi : Function.Injective (A.toContinuousLinearMap - C x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A v - C x v = 0 at hv
    have he : A v = C x v := sub_eq_zero.mp hv
    have hh : ‖v‖ ≤ (‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖) * ‖v‖ := by
      calc
        ‖v‖ = ‖A.symm (A v)‖ := by rw [A.symm_apply_apply]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A v‖ := (A.symm : E →L[ℝ] E).le_opNorm _
        _ = ‖(A.symm : E →L[ℝ] E)‖ * ‖C x v‖ := by rw [he]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (‖C x‖ * ‖v‖) := by gcongr; exact (C x).le_opNorm _
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((‖C‖ * ‖x‖) * ‖v‖) := by gcongr; exact C.le_opNorm _
        _ = _ := by ring
    have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hn
  let e := LinearEquiv.ofBijective (A.toContinuousLinearMap - C x).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma normalJetMap_uniform_inverse (p : E) (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (r : ℝ≥0)
    (hr : ‖C‖₊ * r < ‖(A.symm : E →L[ℝ] E)‖₊⁻¹) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = normalJetMap p A C ∧
      e.source = Metric.ball 0 r ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hf := normalJetMap_approximates p A C r
  let e := hf.toOpenPartialHomeomorph _ _ (Or.inr hr) Metric.isOpen_ball
  refine ⟨e,rfl,rfl,?_⟩
  intro y hy
  have hx : ‖e.symm y‖ < (r : ℝ) := mem_ball_zero_iff.mp (e.map_target hy)
  have hinvpos : 0 < ‖(A.symm : E →L[ℝ] E)‖₊ := by
    by_contra hp
    have hn : ‖(A.symm : E →L[ℝ] E)‖₊ = 0 := le_antisymm (not_lt.mp hp) zero_le
    simp only [hn, _root_.inv_zero] at hr
    exact (not_lt_of_ge zero_le) hr
  have hmul : ‖(A.symm : E →L[ℝ] E)‖ * (‖C‖ * (r : ℝ)) < 1 := by
    have h := (lt_inv_mul_iff₀ hinvpos).mp (show ‖C‖₊ * r < ‖(A.symm : E →L[ℝ] E)‖₊⁻¹ * 1 by simpa only [mul_one] using hr)
    exact_mod_cast h
  have hsmall : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖e.symm y‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le (mul_nonneg (norm_nonneg (A.symm : E →L[ℝ] E)) (norm_nonneg C)))
      (by simpa only [mul_assoc] using hmul)
  obtain ⟨d,hd⟩ := normalJetMap_derivative_invertible A C hsmall
  have hder := hasFDerivAt_normalJetMap p A C hC (e.symm y)
  rw [←hd] at hder
  exact (e.contDiffAt_symm hy hder (contDiff_normalJetMap p A C).contDiffAt).contDiffWithinAt
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_first_phase_jet (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    fderiv ℝ (φ ∘ normalJetMap p A C) 0 v = fderiv ℝ φ p (A v) := by
  rw [fderiv_comp 0 (hφ.differentiable (by simp) _)
    ((contDiff_normalJetMap p A C).differentiable (by simp) _),fderiv_normalJetMap _ _ _ hC]
  simp [normalJetMap_zero]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_second_phase_jet (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v w : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ normalJetMap p A C)) 0 v w =
      fderiv ℝ (fderiv ℝ φ) p (A v) (A w) - fderiv ℝ φ p (C v w) := by
  let F := normalJetMap p A C
  have he : fderiv ℝ (φ ∘ F) = fun y => (fderiv ℝ φ (F y)).comp (A-C y) := by
    funext y
    rw [fderiv_comp y (hφ.differentiable (by simp) _) ((contDiff_normalJetMap p A C).differentiable (by simp) _)]
    rw [fderiv_normalJetMap _ _ _ hC]
  have hF : HasFDerivAt F A 0 := by
    simpa only [map_zero,sub_zero] using hasFDerivAt_normalJetMap p A C hC 0
  have hd := ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (F 0)).hasFDerivAt
  have hA := (hasFDerivAt_const A (0 : E)).sub C.hasFDerivAt
  have hh := ((hd.comp 0 hF).clm_comp hA).fderiv
  simp only [Function.comp_def, Pi.sub_apply] at hh
  rw [he,hh]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,map_zero,
    sub_zero,zero_sub,_root_.neg_apply,normalJetMap_zero,F]
  simp [sub_eq_add_neg,add_comm]

lemma metricNormal_second_phase_jet (g : SmoothMetric E E) (p : E) (A : E →L[ℝ] E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v w : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ normalJetMap p A ((metricChristoffel g p).bilinearComp A A))) 0 v w =
      fderiv ℝ (fderiv ℝ φ) p (A v) (A w) -
        fderiv ℝ φ p (metricChristoffel g p (A v) (A w)) :=
  normalJetMap_second_phase_jet p A ((metricChristoffel g p).bilinearComp A A)
    (fun v w => metricChristoffel_symm g p (A v) (A w)) hφ v w


end YauCounterexamples
end

end OAI
