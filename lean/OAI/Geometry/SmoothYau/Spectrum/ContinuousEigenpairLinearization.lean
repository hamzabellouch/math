import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoefficientGradientApply
import OAI.Geometry.SmoothYau.Geometry.CoordinateGradientPairScalarCorrection
import OAI.Geometry.SmoothYau.Geometry.LocalizeRepresentative
import OAI.Geometry.SmoothYau.Spectrum.SpectralResolvent

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma compact_eigenspace_finite (T : X →L[ℝ] X) (hT : IsCompactOperator T)
    {μ : ℝ} (hμ : μ ≠ 0) : FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (Module.End.eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [Module.End.restrict_eigenspace, LinearMap.coe_smul,
    IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

structure PositivePairing where
  form : X →L[ℝ] X →L[ℝ] ℝ
  symmetric : ∀ x y, form x y = form y x
  positive : ∀ x, x ≠ 0 → 0 < form x x

namespace PositivePairing
variable (B : PositivePairing (X := X))

def perpendicular (u : X) : Submodule ℝ X := (B.form u).ker

instance perpendicular_complete (u : X) : CompleteSpace (B.perpendicular u) :=
  (B.form u).isClosed_ker.completeSpace_coe

omit [CompleteSpace X] in
lemma perpendicular_invariant (T : X →L[ℝ] X)
    (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} {u : X} (hu : T u = μ • u) :
    ∀ v ∈ B.perpendicular u, T v ∈ B.perpendicular u := by
  intro v hv
  change B.form u (T v) = 0
  change B.form u v = 0 at hv
  rw [← hsym, hu, map_smul, _root_.smul_apply, hv, smul_zero]

theorem simple_eigenvalue_complement_invertible (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    IsUnit (T.restrict (B.perpendicular_invariant T hsym hu) - μ • 1) := by
  let R := T.restrict (B.perpendicular_invariant T hsym hu)
  have hR : IsCompactOperator R := hT.restrict' (B.perpendicular_invariant T hsym hu)
  have hno : ¬ Module.End.HasEigenvalue R.toLinearMap μ := by
    intro he
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    have heq : T (v : X) = μ • (v : X) := by
      have hh := Module.End.mem_eigenspace_iff.mp hv
      exact congrArg Subtype.val hh
    obtain ⟨c, hc⟩ := hsimple v heq
    have hb : B.form u (v : X) = 0 := v.property
    rw [hc, map_smul, smul_eq_mul] at hb
    have hc0 : c = 0 := (mul_eq_zero.mp hb).resolve_right (B.positive u hu0).ne'
    apply hv0
    apply Subtype.ext
    simpa only [hc0, zero_smul, Submodule.coe_zero] using hc
  have hr := (hR.hasEigenvalue_or_mem_resolventSet hμ).resolve_left hno
  rw [spectrum.mem_resolventSet_iff] at hr
  have hh : R - μ • 1 = -(algebraMap ℝ _ μ - R) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hh]
  exact hr.neg
end PositivePairing

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def realRepresentative (s : ℝ) : A.realH s →L[ℝ] (M →ᵇ ℝ) :=
  Complex.reCLM.compLeftContinuousBounded M ∘L A.representative s ∘L (A.realH s).subtypeL

omit [T2Space M] in
lemma realRepresentative_apply (s : ℝ) (u : A.realH s) (x : M) :
    A.realRepresentative s u x = A.realValue s u x := rfl

omit [T2Space M] in
lemma realRepresentative_injective (s : ℝ) (ht : Module.finrank ℝ E < 2 * s) :
    Injective (A.realRepresentative s) := by
  intro u v huv
  apply Subtype.ext
  apply manifoldSobolevRepresentative_injective A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht
  ext x
  change A.representative s u x = A.representative s v x
  rw [← A.ofReal_realValue s u x, ← A.ofReal_realValue s v x]
  exact congrArg (fun f : M →ᵇ ℝ => (f x : ℂ)) huv

def intrinsicForm (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ) :
    A.realH s →L[ℝ] A.realH s →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (A.realH s) (M →ᵇ ℝ) ℝ (I.integralCLM g) ∘L
    (ContinuousLinearMap.mul ℝ (M →ᵇ ℝ)).bilinearComp (A.realRepresentative s) (A.realRepresentative s)

omit [T2Space M] in
lemma intrinsicForm_apply (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ)
    (u v : A.realH s) :
    A.intrinsicForm I s u v = I.mean g (fun x => A.realValue s u x * A.realValue s v x) := rfl

def intrinsicPairing (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ)
    (ht : Module.finrank ℝ E < 2 * s) : PositivePairing (X := A.realH s) where
  form := A.intrinsicForm I s
  symmetric := by
    intro u v
    rw [A.intrinsicForm_apply, A.intrinsicForm_apply]
    congr 1
    funext x
    exact mul_comm _ _
  positive := by
    intro u hu
    change 0 < I.integral g (A.realRepresentative s u * A.realRepresentative s u)
    apply I.integral_pos g (fun x => mul_self_nonneg _)
    have hne : A.realRepresentative s u ≠ 0 := by
      intro he
      apply hu
      apply A.realRepresentative_injective s ht
      simpa using he
    have hx : ∃ x, A.realRepresentative s u x ≠ 0 := by
      by_contra! hh
      apply hne
      ext x
      exact hh x
    obtain ⟨x,hx⟩ := hx
    exact ⟨x, mul_self_pos.mpr hx⟩

def realSpectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.realInclusion ∘L A.realResolvent B α hα0 hα he

lemma realSpectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    IsCompactOperator (A.realSpectralResolvent B α hα0 hα he) := by
  have hc := A.spectralResolvent_compact B α hα he
  have hr : ∀ u ∈ A.realH (2 * (k : ℝ)), A.spectralResolvent B α hα he u ∈ A.realH (2 * (k : ℝ)) := by
    intro u hu x
    change (A.representative _ (A.inclusion (A.resolvent B α hα he u)) x).im = 0
    rw [A.inclusion_representative]
    exact A.resolvent_mem_realH B α hα0 hα he ⟨u, hu⟩ x
  exact hc.restrict' hr
end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
omit [T2Space M] in
lemma mean_sub (f h : M → ℝ) (hf : Continuous f) (hh : Continuous h) :
    I.mean g (fun x => f x - h x) = I.mean g f - I.mean g h := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  let H := BoundedContinuousFunction.mkOfCompact ⟨h,hh⟩
  change I.integralCLM g (F - H) = I.integralCLM g F - I.integralCLM g H
  exact map_sub _ _ _
omit [T2Space M] in
lemma mean_const_mul (c : ℝ) (f : M → ℝ) (hf : Continuous f) :
    I.mean g (fun x => c * f x) = c * I.mean g f := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  change I.integralCLM g (c • F) = c • I.integralCLM g F
  exact map_smul _ _ _
end MetricIntegralAtlas
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem realSpectralResolvent_symmetric (I : MetricIntegralAtlas (E := E) (M := M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u v : A.realH (2 * (k : ℝ))) :
    A.intrinsicForm I (2 * (k : ℝ)) (A.realSpectralResolvent B α hα0 hα he u) v =
      A.intrinsicForm I (2 * (k : ℝ)) u (A.realSpectralResolvent B α hα0 hα he v) := by
  let R := A.realResolvent B α hα0 hα he
  let U := A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (R u)
  let V := A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (R v)
  let f := A.realValue (2 * (k : ℝ)) u
  let h := A.realValue (2 * (k : ℝ)) v
  have hU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 U := A.realValue_C2 _
  have hV : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 V := A.realValue_C2 _
  have hf : Continuous f := (A.realRepresentative _ u).continuous
  have hh : Continuous h := (A.realRepresentative _ v).continuous
  have heU : laplaceBeltrami g U = fun x => α * U x - f x := by
    funext x
    have hx := A.realResolvent_value B α hα0 hα he u x
    change α * U x - laplaceBeltrami g U x = f x at hx
    linarith
  have heV : laplaceBeltrami g V = fun x => α * V x - h x := by
    funext x
    have hx := A.realResolvent_value B α hα0 hα he v x
    change α * V x - laplaceBeltrami g V x = h x at hx
    linarith
  have hdU : Continuous (laplaceBeltrami g U) := by rw [heU]; exact (continuous_const.mul hU.continuous).sub hf
  have hdV : Continuous (laplaceBeltrami g V) := by rw [heV]; exact (continuous_const.mul hV.continuous).sub hh
  rw [A.intrinsicForm_apply, A.intrinsicForm_apply]
  simp only [realSpectralResolvent, ContinuousLinearMap.comp_apply, A.realValue_inclusion]
  change I.mean g (fun x => U x * h x) = I.mean g (fun x => f x * V x)
  have hleft : (fun x => U x * h x) = fun x => α * (U x * V x) - U x * laplaceBeltrami g V x := by
    funext x; rw [heV]; ring
  have hright : (fun x => f x * V x) = fun x => α * (U x * V x) - laplaceBeltrami g U x * V x := by
    funext x; rw [heU]; ring
  rw [hleft, hright, I.mean_sub g (fun x => α * (U x * V x)) (fun x => U x * laplaceBeltrami g V x)
      (continuous_const.mul (hU.continuous.mul hV.continuous)) (hU.continuous.mul hdV),
    I.mean_sub g (fun x => α * (U x * V x)) (fun x => laplaceBeltrami g U x * V x)
      (continuous_const.mul (hU.continuous.mul hV.continuous)) (hdU.mul hV.continuous),
    I.laplacian_symmetric_C2 g hU hV]
end CompactMetricAtlas

end

section
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
namespace PositivePairing
variable (B : PositivePairing (X := X))

def eigenpairLinearization (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    (ℝ × X) →L[ℝ] (ℝ × X) :=
  ((B.form u).comp (ContinuousLinearMap.snd ℝ ℝ X)).prod
    (((T - μ • 1).comp (ContinuousLinearMap.snd ℝ ℝ X)) -
      (ContinuousLinearMap.toSpanSingleton ℝ u).comp (ContinuousLinearMap.fst ℝ ℝ X))

omit [CompleteSpace X] in
lemma eigenpairLinearization_apply (T : X →L[ℝ] X) (μ : ℝ) (u : X) (a : ℝ) (v : X) :
    B.eigenpairLinearization T μ u (a,v) = (B.form u v, T v - μ • v - a • u) := rfl

lemma eigenpairLinearization_bijective (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    Bijective (B.eigenpairLinearization T μ u) := by
  have hpos := B.positive u hu0
  have hφ : ∀ v, B.form u (T v - μ • v) = 0 := by
    intro v
    rw [map_sub, ← hsym, hu, map_smul, _root_.smul_apply, map_smul]
    exact sub_self _
  have hinj : Injective (B.eigenpairLinearization T μ u) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨a,v⟩ hv
    have hv1 : B.form u v = 0 := congrArg Prod.fst hv
    have hv2 : T v - μ • v - a • u = 0 := congrArg Prod.snd hv
    have hfa := congrArg (B.form u) hv2
    rw [map_sub, hφ, map_smul, map_zero, smul_eq_mul, zero_sub, neg_eq_zero] at hfa
    have ha : a = 0 := (mul_eq_zero.mp hfa).resolve_right hpos.ne'
    have he : T v = μ • v := by simpa only [ha, zero_smul, sub_zero, sub_eq_zero] using hv2
    obtain ⟨c, hc⟩ := hsimple v he
    rw [hc, map_smul, smul_eq_mul] at hv1
    have hc0 : c = 0 := (mul_eq_zero.mp hv1).resolve_right hpos.ne'
    simp [ha, hc, hc0]
  refine ⟨hinj, ?_⟩
  rintro ⟨c,y⟩
  let b := B.form u y / B.form u u
  let z : B.perpendicular u := ⟨y - b • u, by
    change B.form u (y - b • u) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    dsimp [b]
    rw [div_mul_cancel₀ _ hpos.ne', sub_self]⟩
  have hi := B.simple_eigenvalue_complement_invertible T hT hsym hμ hu0 hu hsimple
  obtain ⟨w, hw⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2 z
  have hw' : T (w : X) - μ • (w : X) = y - b • u := congrArg Subtype.val hw
  refine ⟨(-b, (c / B.form u u) • u + (w : X)), ?_⟩
  apply Prod.ext
  · change B.form u ((c / B.form u u) • u + (w : X)) = c
    rw [map_add, map_smul, smul_eq_mul, show B.form u (w : X) = 0 from w.property,
      add_zero, div_mul_cancel₀ _ hpos.ne']
  · change T ((c / B.form u u) • u + (w : X)) -
      μ • ((c / B.form u u) • u + (w : X)) - (-b) • u = y
    rw [map_add, map_smul, hu, smul_add, neg_smul, sub_neg_eq_add,
      smul_comm (c / B.form u u) μ u]
    have hh : μ • ((c / B.form u u) • u) + T (w : X) -
        (μ • ((c / B.form u u) • u) + μ • (w : X)) = T (w : X) - μ • (w : X) := by abel
    rw [hh, hw', sub_add_cancel]

abbrev EigenpairParameters := (X →L[ℝ] X) × (ℝ × X)

def eigenpairMap (u : X) (p : EigenpairParameters (X := X)) : EigenpairParameters (X := X) :=
  (p.1, (B.form u p.2.2, p.1 p.2.2 - p.2.1 • p.2.2))

def eigenpairDerivative (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    EigenpairParameters (X := X) →L[ℝ] EigenpairParameters (X := X) :=
  let F := ContinuousLinearMap.fst ℝ (X →L[ℝ] X) (ℝ × X)
  let S := ContinuousLinearMap.snd ℝ (X →L[ℝ] X) (ℝ × X)
  F.prod (((B.eigenpairLinearization T μ u).comp S) +
    (0 : EigenpairParameters (X := X) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.apply ℝ X u).comp F))

omit [CompleteSpace X] in
lemma eigenpairDerivative_apply (T : X →L[ℝ] X) (μ : ℝ) (u : X)
    (H : X →L[ℝ] X) (b : ℝ) (v : X) :
    B.eigenpairDerivative T μ u (H,(b,v)) =
      (H,(B.form u v,T v - μ • v - b • u + H u)) := by
  simp [eigenpairDerivative, eigenpairLinearization]

lemma eigenpairDerivative_bijective (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    Bijective (B.eigenpairDerivative T μ u) := by
  have hL := B.eigenpairLinearization_bijective T hT hsym hμ hu0 hu hsimple
  refine ⟨?_, ?_⟩
  · rintro ⟨H,b,v⟩ ⟨K,c,w⟩ he
    simp only [B.eigenpairDerivative_apply] at he
    have hHK : H = K := congrArg Prod.fst he
    subst K
    have hvw : B.eigenpairLinearization T μ u (b,v) =
        B.eigenpairLinearization T μ u (c,w) := by
      apply Prod.ext
      · exact congrArg (fun p : EigenpairParameters (X := X) => p.2.1) he
      · exact add_right_cancel (congrArg (fun p : EigenpairParameters (X := X) => p.2.2) he)
    exact congrArg (fun p : ℝ × X => (H,p)) (hL.1 hvw)
  · rintro ⟨H,c,y⟩
    obtain ⟨⟨b,v⟩, he⟩ := hL.2 (c, y - H u)
    refine ⟨(H,(b,v)), ?_⟩
    rw [B.eigenpairDerivative_apply]
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change B.form u v = c at he1
    change T v - μ • v - b • u = y - H u at he2
    rw [he1, he2, sub_add_cancel]

omit [CompleteSpace X] in
lemma eigenpairMap_hasStrictFDerivAt (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    HasStrictFDerivAt (B.eigenpairMap u) (B.eigenpairDerivative T μ u) (T,(μ,u)) := by
  let F := ContinuousLinearMap.fst ℝ (X →L[ℝ] X) (ℝ × X)
  let S := ContinuousLinearMap.snd ℝ (X →L[ℝ] X) (ℝ × X)
  let V := (ContinuousLinearMap.snd ℝ ℝ X).comp S
  let L := (ContinuousLinearMap.fst ℝ ℝ X).comp S
  have hh := F.hasStrictFDerivAt (x := (T,(μ,u))) |>.prodMk
    (((B.form u).hasStrictFDerivAt.comp (T,(μ,u)) V.hasStrictFDerivAt).prodMk
      ((F.hasStrictFDerivAt.clm_apply V.hasStrictFDerivAt).sub
        (L.hasStrictFDerivAt.smul V.hasStrictFDerivAt)))
  convert! hh using 1
  ext <;>
      simp [eigenpairDerivative, eigenpairLinearization, F,S,V,L]

theorem simple_eigenpair_persistence (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    ∃ (e : (X →L[ℝ] X) → ℝ) (v : (X →L[ℝ] X) → X),
      e T = μ ∧ v T = u ∧ ContinuousAt e T ∧ ContinuousAt v T ∧
      ∀ᶠ R in 𝓝 T, v R ≠ 0 ∧ R (v R) = e R • v R ∧ B.form u (v R) = B.form u u := by
  have hbij := B.eigenpairDerivative_bijective T hT hsym hμ hu0 hu hsimple
  let D := ContinuousLinearEquiv.ofBijective (B.eigenpairDerivative T μ u)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hd : HasStrictFDerivAt (B.eigenpairMap u) (D : _ →L[ℝ] _) (T,(μ,u)) :=
    B.eigenpairMap_hasStrictFDerivAt T μ u
  let inv := hd.localInverse (B.eigenpairMap u) D (T,(μ,u))
  let z : (X →L[ℝ] X) → EigenpairParameters (X := X) := fun R => (R,(B.form u u,0))
  have hzT : z T = B.eigenpairMap u (T,(μ,u)) := by simp [z,eigenpairMap,hu]
  have hz : ContinuousAt z T := continuousAt_id.prodMk continuousAt_const
  have hval : inv (z T) = (T,(μ,u)) := by rw [hzT]; exact hd.localInverse_apply_image
  have hc : ContinuousAt (fun R => inv (z R)) T := by
    have hci : ContinuousAt inv (z T) := by
      rw [hzT]
      exact hd.localInverse_continuousAt
    exact hci.comp hz
  refine ⟨fun R => (inv (z R)).2.1, fun R => (inv (z R)).2.2,
    congrArg (fun p => p.2.1) hval, congrArg (fun p => p.2.2) hval,
    hc.snd.fst, hc.snd.snd, ?_⟩
  have he : ∀ᶠ R in 𝓝 T, B.eigenpairMap u (inv (z R)) = z R := by
    have hzt : Tendsto z (𝓝 T) (𝓝 (B.eigenpairMap u (T,(μ,u)))) := hzT ▸ hz
    exact hzt.eventually hd.eventually_right_inverse
  filter_upwards [he] with R hR
  have hR1 : (inv (z R)).1 = R := congrArg Prod.fst hR
  have hR2 : B.form u (inv (z R)).2.2 = B.form u u := congrArg (fun p => p.2.1) hR
  have hR3 : (inv (z R)).1 (inv (z R)).2.2 -
      (inv (z R)).2.1 • (inv (z R)).2.2 = 0 := congrArg (fun p => p.2.2) hR
  rw [hR1, sub_eq_zero] at hR3
  refine ⟨?_, hR3, hR2⟩
  intro hn
  rw [hn, map_zero] at hR2
  exact (B.positive u hu0).ne' hR2.symm

end PositivePairing

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
namespace PositivePairing
variable (B : PositivePairing (X := X))

omit [CompleteSpace X] in
lemma continuous_eigenpairLinearization :
    Continuous (fun p : EigenpairParameters (X := X) => B.eigenpairLinearization p.1 p.2.1 p.2.2) := by
  have hB : Continuous (fun p : EigenpairParameters (X := X) => B.form p.2.2) :=
    B.form.continuous.comp continuous_snd.snd
  have hS : Continuous (fun p : EigenpairParameters (X := X) =>
      ContinuousLinearMap.toSpanSingleton ℝ p.2.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ X).continuous.comp continuous_snd.snd
  have h1 : Continuous (fun p : EigenpairParameters (X := X) =>
      (B.form p.2.2).comp (ContinuousLinearMap.snd ℝ ℝ X)) :=
    hB.clm_comp continuous_const
  have h2 : Continuous (fun p : EigenpairParameters (X := X) =>
      ((p.1 - p.2.1 • (1 : X →L[ℝ] X)).comp (ContinuousLinearMap.snd ℝ ℝ X)) -
        (ContinuousLinearMap.toSpanSingleton ℝ p.2.2).comp (ContinuousLinearMap.fst ℝ ℝ X)) :=
    ((continuous_fst.sub (continuous_snd.fst.smul continuous_const)).clm_comp continuous_const).sub
      (hS.clm_comp continuous_const)
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (h1.prodMk h2)

omit [CompleteSpace X] in
lemma simple_of_linearization_injective (T : X →L[ℝ] X) {μ : ℝ} {u : X}
    (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hi : Injective (B.eigenpairLinearization T μ u)) :
    ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u := by
  intro v hv
  let c := B.form u v / B.form u u
  have hc : B.form u v - c * B.form u u = 0 := by
    dsimp [c]
    rw [div_mul_cancel₀ _ (B.positive u hu0).ne', sub_self]
  have he : B.eigenpairLinearization T μ u (0,v - c • u) = 0 := by
    rw [B.eigenpairLinearization_apply]
    apply Prod.ext
    · simpa only [map_sub, map_smul, smul_eq_mul, Prod.fst_zero] using hc
    · simp only [map_sub, map_smul, hv, hu, smul_sub, zero_smul, sub_zero]
      rw [smul_comm c μ u]
      exact sub_self _
  have hz : v - c • u = 0 := congrArg Prod.snd (hi (he.trans (map_zero _).symm))
  exact ⟨c, sub_eq_zero.mp hz⟩

lemma eigenpair_linearization_units_eventually (T : X →L[ℝ] X)
    (e : (X →L[ℝ] X) → ℝ) (v : (X →L[ℝ] X) → X)
    (hce : ContinuousAt e T) (hcv : ContinuousAt v T)
    (hunit : IsUnit (B.eigenpairLinearization T (e T) (v T))) :
    ∀ᶠ R in 𝓝 T, IsUnit (B.eigenpairLinearization R (e R) (v R)) := by
  have hparam : ContinuousAt (fun R : X →L[ℝ] X => (R, (e R, v R))) T :=
    continuousAt_id.prodMk (hce.prodMk hcv)
  have ho : IsOpen {p : EigenpairParameters (X := X) |
      IsUnit (B.eigenpairLinearization p.1 p.2.1 p.2.2)} :=
    Units.isOpen.preimage B.continuous_eigenpairLinearization
  exact hparam.eventually (ho.mem_nhds hunit)

theorem simple_eigenpair_persistence_with_simplicity (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    ∃ (e : (X →L[ℝ] X) → ℝ) (v : (X →L[ℝ] X) → X),
      e T = μ ∧ v T = u ∧ ContinuousAt e T ∧ ContinuousAt v T ∧
      ∀ᶠ R in 𝓝 T, v R ≠ 0 ∧ R (v R) = e R • v R ∧
        B.form u (v R) = B.form u u ∧
        ∀ w, R w = e R • w → ∃ c : ℝ, w = c • v R := by
  obtain ⟨e,v,he,hv,hce,hcv,hpair⟩ :=
    B.simple_eigenpair_persistence T hT hsym hμ hu0 hu hsimple
  have hunit : IsUnit (B.eigenpairLinearization T (e T) (v T)) := by
    rw [he,hv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      (B.eigenpairLinearization_bijective T hT hsym hμ hu0 hu hsimple)
  have hevent := B.eigenpair_linearization_units_eventually T e v hce hcv hunit
  refine ⟨e,v,he,hv,hce,hcv,?_⟩
  filter_upwards [hpair,hevent] with R hp hi
  exact ⟨hp.1,hp.2.1,hp.2.2,
    B.simple_of_linearization_injective R hp.1 hp.2.1 (ContinuousLinearMap.isUnit_iff_bijective.mp hi).1⟩
end PositivePairing


end YauCounterexamples
end

end OAI
