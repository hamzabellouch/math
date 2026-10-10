import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ClmMatrixAlgHom
import OAI.Geometry.SmoothYau.Estimates.DerivExpSmulZero
import OAI.Geometry.SmoothYau.Estimates.UniformDifferenceQuotient
import OAI.Geometry.SmoothYau.Geometry.CoordinateGradientPairScalarCorrection
import OAI.Geometry.SmoothYau.Smoothness.BundleMetricInner
import OAI.Geometry.SmoothYau.Smoothness.IteratedFDerivCompClm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def pinnedMetric (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) : SmoothMetric E M :=
  exponentialMetric g (fun x => (-t/2) • K x) (hK.const_smul_section (a := -t/2))

lemma pinnedMetric_inner (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w =
      g.inner x ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) v)
        ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) w) := rfl

lemma pinnedMetric_unchanged (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) (x : M) (hx : K x = 0) :
    (pinnedMetric g K hK t).inner x = g.inner x := by
  ext v w
  rw [pinnedMetric_inner,hx]
  change g.inner x ((NormedSpace.exp ((-t/2) • (0 : E →L[ℝ] E))) (show E from v))
    ((NormedSpace.exp ((-t/2) • (0 : E →L[ℝ] E))) (show E from w)) = _
  rw [smul_zero, NormedSpace.exp_zero]
  rfl

lemma pinnedMetric_preserves_gradient_pairing (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) (x : M)
    (hsa : ∀ v w, g.inner x (K x v) w = g.inner x v (K x w))
    {v : TangentSpace 𝓘(ℝ,E) x} (hv : K x v = 0) (w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w = g.inner x v w := by
  rw [pinnedMetric_inner]
  apply pinned_exp_pairing (E := E)
  · intro a b
    change g.inner x ((-t/2) • K x a) b = g.inner x a ((-t/2) • K x b)
    erw [map_smul, smul_apply, map_smul]
    exact congrArg (fun r : ℝ => (-t/2) • r) (hsa a b)
  · change (-t/2) • K x v = 0
    rw [hv,smul_zero]

lemma pinnedMetric_first_variation (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (x : M)
    (hsa : ∀ v w, g.inner x (K x v) w = g.inner x v (K x w))
    (v w : TangentSpace 𝓘(ℝ,E) x) :
    HasDerivAt (fun t => (pinnedMetric g K hK t).inner x v w)
      (-g.inner x (K x v) w) 0 := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  let A : E →L[ℝ] E := K x
  change HasDerivAt (fun t : ℝ => G ((NormedSpace.exp ((-t/2) • A)) v)
    ((NormedSpace.exp ((-t/2) • A)) w)) (-G (A v) w) 0
  have hsa' : ∀ (a b : E), G (A a) b = G a (A b) := hsa
  have hb := exp_pairing_first_variation G ((-1/2 : ℝ) • A) v w
  have hm (t : ℝ) : t • ((-1/2 : ℝ) • A) = (-t/2) • A := by
    rw [smul_smul]
    congr 1
    ring
  simp only [hm] at hb
  have hc (a b : E) : G (((-1/2:ℝ) • A) a) b + G a (((-1/2:ℝ) • A) b) = -G (A a) b := by
    simp only [_root_.smul_apply, map_smul, smul_eq_mul, ← hsa' a b]
    ring
  erw [hc] at hb
  exact hb


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma contMDiffAt_exp_along {f : D → M}
    (K : ∀ z, TangentSpace 𝓘(ℝ,E) (f z) →L[ℝ] TangentSpace 𝓘(ℝ,E) (f z)) {z₀ : D}
    (hk : ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀) :
    ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, (show E →L[ℝ] E from NormedSpace.exp (show E →L[ℝ] E from K z))⟩ :
        TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀ := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiff
  rw [contMDiffAt_totalSpace] at hk ⊢
  refine ⟨hk.1, ?_⟩
  have hh := he.contMDiff.contMDiffAt.comp z₀ hk.2
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ (f z₀))
  filter_upwards [hk.1.continuousAt.preimage_mem_nhds hn] with z hz
  change f z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).baseSet at hz
  simp only [Function.comp_def,hom_trivializationAt_apply]
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  let e : E ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (f z₀)).continuousLinearEquivAt ℝ (f z) hz
  have hm := NormedSpace.map_exp e.conjContinuousAlgEquiv
    (e.arrowCongr e).continuous (show E →L[ℝ] E from K z)
  erw [ContinuousLinearMap.inCoordinates_eq hz hz,
    ContinuousLinearMap.inCoordinates_eq hz hz]
  convert hm using 1 <;> rfl

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_smul_along {f : D → M}
    (K : ∀ z, TangentSpace 𝓘(ℝ,E) (f z) →L[ℝ] TangentSpace 𝓘(ℝ,E) (f z)) {z₀ : D}
    (hk : ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀)
    {a : D → ℝ} (ha : ContMDiffAt 𝓘(ℝ,D) 𝓘(ℝ,ℝ) ∞ a z₀) :
    ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, a z • K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀ := by
  rw [contMDiffAt_totalSpace] at hk ⊢
  refine ⟨hk.1, (ha.smul hk.2).congr_of_eventuallyEq ?_⟩
  have hn := (trivializationAt (E →L[ℝ] E)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (f z₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ (f z₀))
  filter_upwards [hk.1.continuousAt.preimage_mem_nhds hn] with z hz
  change f z ∈ (trivializationAt (E →L[ℝ] E)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (f z₀)).baseSet at hz
  exact (Trivialization.linear ℝ _ hz).2 _ _

theorem pinnedMetric_joint_coefficients (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (p : M) (i j : CoordIndex E) (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (pinnedMetric g K hK z.1) p z.2 i j) (t,y) := by
  have hs : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ (fun z : ℝ × E => z.2) (t,y) :=
    contDiffAt_snd.contMDiffAt
  have hf : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun z : ℝ × E => (chartAt E p).symm z.2) (t,y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy).comp (t,y) hs
  have hk := (hK _).comp (t,y) hf
  have ha : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ × E => -z.1/2) (t,y) :=
    (contDiffAt_fst.neg.div_const 2).contMDiffAt
  have he := contMDiffAt_exp_along _ (contMDiffAt_smul_along _ hk ha)
  have hi := (contMDiffAt_coordinateVector p i hy).comp (t,y) hs
  have hj := (contMDiffAt_coordinateVector p j hy).comp (t,y) hs
  have hh := ((g.contMDiff _).comp (t,y) hf).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (he.clm_bundle_apply hi) (he.clm_bundle_apply hj)
  rw [contMDiffAt_totalSpace] at hh
  exact contMDiffAt_iff_contDiffAt.mp hh.2

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma pinnedMetric_coefficients_zero (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (p : M) (y : E) :
    metricCoefficients (pinnedMetric g K hK 0) p y = metricCoefficients g p y := by
  ext i j
  simp only [metricCoefficients,pinnedMetric_inner,neg_zero,zero_div]
  erw [zero_smul, NormedSpace.exp_zero]
  rfl

theorem pinnedMetric_eventually_neighborhood (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    {N : Set (SmoothMetric E M)} (hN : IsSmoothNeighborhood g N) :
    ∀ᶠ t in 𝓝 (0 : ℝ), pinnedMetric g K hK t ∈ N := by
  obtain ⟨tests,ε,hε,hN⟩ := hN
  have hq (q : CoordinateTest E M) : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ q.compactSet,
      ‖iteratedFDeriv ℝ q.order (fun z =>
        metricCoefficients (pinnedMetric g K hK t) q.center z q.row q.column -
        metricCoefficients g q.center z q.row q.column) y‖ < ε := by
    have hh := compact_parameter_jets q.isCompact
      (fun y hy => pinnedMetric_joint_coefficients g K hK q.center q.row q.column 0 (q.inTarget hy))
      q.order hε
    simpa only [pinnedMetric_coefficients_zero] using hh
  have hl (l : List (CoordinateTest E M)) : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ q ∈ l, ∀ y ∈ q.compactSet,
        ‖iteratedFDeriv ℝ q.order (fun z =>
          metricCoefficients (pinnedMetric g K hK t) q.center z q.row q.column -
          metricCoefficients g q.center z q.row q.column) y‖ < ε := by
    induction l with
    | nil => simp
    | cons q l ih =>
      filter_upwards [hq q,ih] with t ht hl
      intro q' hq'
      rcases List.mem_cons.mp hq' with h | h
      · subst q'; exact ht
      · exact hl q' h
  filter_upwards [hl tests] with t ht
  exact hN _ ht

end


section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartTangentBasis (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    Module.Basis (CoordIndex E) ℝ E := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y
  have he : (chartAt E p).MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) :=
    ⟨(contMDiffOn_chart (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableOn (by simp)⟩
  have hi : Function.Bijective D := he.symm.mfderiv_bijective hy
  exact (Module.finBasis ℝ E).map (LinearEquiv.ofBijective D.toLinearMap hi)

lemma chartTangentBasis_apply (p : M) (y : E) (hy : y ∈ (chartAt E p).target)
    (i : CoordIndex E) : chartTangentBasis p y hy i = coordinateVector p y i := rfl

lemma pinnedMetric_det (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (pinnedMetric g K hK t) p y).det =
      (metricCoefficients g p y).det := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  let A : E →L[ℝ] E := K ((chartAt E p).symm y)
  have ht : LinearMap.trace ℝ E (((-t/2) • A).toLinearMap) = 0 := by
    change LinearMap.trace ℝ E ((-t/2) • A.toLinearMap) = 0
    rw [map_smul,htr,smul_zero]
  exact tracefree_exp_preserves_gram_det (chartTangentBasis p y hy) G ((-t/2) • A) ht


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff Matrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma metricGradient_coordinate_pairing (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    g.inner ((chartAt E p).symm y) (metricGradient g u ((chartAt E p).symm y))
      (coordinateVector p y i) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) := by
  rw [metricGradient_pairing]
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at hh
  rw [hh]
  rfl

lemma metricGradient_coordinates (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) =
      (chartTangentBasis p y hy).equivFun
        (show E from metricGradient g u ((chartAt E p).symm y)) := by
  let b := chartTangentBasis p y hy
  let v : E := metricGradient g u ((chartAt E p).symm y)
  have he : (metricCoefficients g p y) *ᵥ (b.equivFun v) =
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) := by
    ext i
    rw [← metricGradient_coordinate_pairing g hu p y hy i]
    change (∑ j, g.inner ((chartAt E p).symm y) (b i) (b j) * b.equivFun v j) =
      g.inner ((chartAt E p).symm y) v (b i)
    rw [g.symm _ v (b i)]
    conv_rhs => arg 2; rw [← b.sum_repr v]
    have hsum (L : E →L[ℝ] ℝ) :
        (∑ j, L (b j) * b.repr v j) = L (∑ j, b.repr v j • b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact hsum (g.inner ((chartAt E p).symm y) (b i))
  rw [← he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne'),Matrix.one_mulVec]

lemma pinnedMetric_gradient (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (u : M → ℝ) (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
    metricGradient (pinnedMetric g K hK t) u x = metricGradient g u x := by
  symm
  apply metricGradient_unique
  intro w
  rw [pinnedMetric_preserves_gradient_pairing g K hK t x (hsa x) (hker x) w,
    metricGradient_pairing]

lemma pinnedMetric_flux (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hker : ∀ x, K x (metricGradient g u x) = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    metricFlux (pinnedMetric g K hK t) u p y i = metricFlux g u p y i := by
  have he : (metricCoefficients (pinnedMetric g K hK t) p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) =
      (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) := by
    rw [metricGradient_coordinates _ hu p y hy,metricGradient_coordinates _ hu p y hy,
      pinnedMetric_gradient g K hK hsa u hker t]
  unfold metricFlux
  rw [pinnedMetric_det g K hK htr t p y hy]
  exact congrArg (fun v : CoordIndex E → ℝ => Real.sqrt (metricCoefficients g p y).det * v i) he

theorem pinnedMetric_laplacian (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
    laplaceBeltrami (pinnedMetric g K hK t) u x = laplaceBeltrami g u x := by
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  change (Real.sqrt (metricCoefficients (pinnedMetric g K hK t) x ((chartAt E x) x)).det)⁻¹ *
      (∑ i, fderiv ℝ (fun y => metricFlux (pinnedMetric g K hK t) u x y i)
        ((chartAt E x) x) (Module.finBasis ℝ E i)) =
    (Real.sqrt (metricCoefficients g x ((chartAt E x) x)).det)⁻¹ *
      (∑ i, fderiv ℝ (fun y => metricFlux g u x y i)
        ((chartAt E x) x) (Module.finBasis ℝ E i))
  rw [pinnedMetric_det g K hK htr t x ((chartAt E x) x) hx]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => metricFlux (pinnedMetric g K hK t) u x y i) =ᶠ[𝓝 ((chartAt E x) x)]
      (fun y => metricFlux g u x y i) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
    exact pinnedMetric_flux g K hK hsa htr hu hker t x y hy i
  rw [he.fderiv_eq]


end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Matrix BoundedContinuousFunction
section ExponentialAlgebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma clm_exp_smul_mul (K : E →L[ℝ] E) (s t : ℝ) :
    NormedSpace.exp (s • K) * NormedSpace.exp (t • K) = NormedSpace.exp ((s+t) • K) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  rw [add_smul]
  exact (NormedSpace.exp_add_of_commute (by
    show (s • K) * (t • K) = (t • K) * (s • K)
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm])).symm
end ExponentialAlgebra
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_eq_inner (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (x : M) :
    coordinateGradientPair g u v x = g.inner x (metricGradient g u x) (metricGradient g v x) := by
  classical
  let y := chartAt E x x
  have hy : y ∈ (chartAt E x).target := (chartAt E x).map_source (mem_chart_source E x)
  have hp : (chartAt E x).symm y = x := (chartAt E x).left_inv (mem_chart_source E x)
  let b := chartTangentBasis x y hy
  have hc := metricGradient_coordinates g hv x y hy
  rw [hp] at hc
  have hdu (i : CoordIndex E) :
      g.inner x (metricGradient g u x) (b i) =
      fderiv ℝ (u ∘ (chartAt E x).symm) y (Module.finBasis ℝ E i) := by
    have hh := metricGradient_coordinate_pairing g hu x y hy i
    rw [hp] at hh
    exact hh
  calc
    coordinateGradientPair g u v x = ∑ i, (fderiv ℝ (u ∘ (chartAt E x).symm) y
        (Module.finBasis ℝ E i)) * (((metricCoefficients g x y)⁻¹) *ᵥ
        (fun j => fderiv ℝ (v ∘ (chartAt E x).symm) y (Module.finBasis ℝ E j))) i := by
      simp only [coordinateGradientPair,Matrix.mulVec,dotProduct,Finset.mul_sum,y]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ = ∑ i, b.equivFun (show E from metricGradient g v x) i *
        g.inner x (metricGradient g u x) (b i) := by
      rw [hc]
      apply Finset.sum_congr rfl; intro i _
      rw [hdu]; ring
    _ = g.inner x (metricGradient g u x) (metricGradient g v x) := by
      let L : E →L[ℝ] ℝ := g.inner x (metricGradient g u x)
      have hh := congrArg L (b.sum_repr (show E from metricGradient g v x))
      change (∑ i, b.repr (show E from metricGradient g v x) i * L (b i)) = L (show E from metricGradient g v x)
      simpa only [map_sum,map_smul,smul_eq_mul] using hh

lemma pinnedMetric_gradient_general (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (u : M → ℝ) (t : ℝ) (x : M) :
    metricGradient (pinnedMetric g K hK t) u x =
      (NormedSpace.exp (t • (show E →L[ℝ] E from K x))) (metricGradient g u x) := by
  symm
  apply metricGradient_unique
  intro w
  erw [pinnedMetric_inner]
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  let A : E →L[ℝ] E := K x
  let V : E := metricGradient g u x
  let W : E := w
  have hs : ∀ a b : E, G (((-t/2) • A) a) b = G a (((-t/2) • A) b) := by
    intro a b
    change g.inner x (((-t/2) • (K x : E →L[ℝ] E)) a) b =
      g.inner x a (((-t/2) • (K x : E →L[ℝ] E)) b)
    erw [smul_apply, smul_apply, map_smul, smul_apply, map_smul]
    exact congrArg (fun r : ℝ => (-t/2) • r) (hsa x a b)
  refine Eq.trans ?_ (metricGradient_pairing g u x w)
  change G ((NormedSpace.exp ((-t/2) • A)) ((NormedSpace.exp (t • A)) V))
    ((NormedSpace.exp ((-t/2) • A)) W) = G V W
  calc
    _ = G (((NormedSpace.exp ((-t/2) • A) * NormedSpace.exp ((-t/2) • A)) *
        NormedSpace.exp (t • A)) V) W := by
      exact (clm_exp_selfAdjoint G ((-t/2) • A) hs
        ((NormedSpace.exp ((-t/2) • A)) ((NormedSpace.exp (t • A)) V)) W).symm
    _ = G V W := by
      rw [clm_exp_smul_mul,clm_exp_smul_mul]
      have he : -t/2 + -t/2 + t = 0 := by ring
      rw [he,zero_smul,NormedSpace.exp_zero,one_apply_eq_self]

lemma pinnedMetric_gradientPair (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (t : ℝ) (x : M) :
    coordinateGradientPair (pinnedMetric g K hK t) u v x =
      g.inner x (metricGradient g u x)
        ((NormedSpace.exp (t • (show E →L[ℝ] E from K x))) (metricGradient g v x)) := by
  rw [coordinateGradientPair_eq_inner _ hu hv,metricGradient_pairing,
    pinnedMetric_gradient_general g K hK hsa]
  exact (metricGradient_pairing g u x _).symm

lemma pinnedMetric_gradientPair_deriv (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (x : M) :
    HasDerivAt (fun t => coordinateGradientPair (pinnedMetric g K hK t) u v x)
      (g.inner x (metricGradient g u x) (K x (metricGradient g v x))) 0 := by
  simp_rw [pinnedMetric_gradientPair g K hK hsa hu hv]
  let L : E →L[ℝ] ℝ := g.inner x (metricGradient g u x)
  exact L.hasFDerivAt.comp_hasDerivAt 0
    (exp_smul_apply_deriv_zero (show E →L[ℝ] E from K x) (show E from metricGradient g v x))
end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction
section PinnedJointEnergy
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (g : SmoothMetric E M)
variable (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
variable (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
  (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
variable (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
variable {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
  (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v)
include hsa hu hv
lemma pinnedMetric_joint_gradientPair (t : ℝ) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => coordinateGradientPair (pinnedMetric g K hK z.1)
      u v ((chartAt E p).symm z.2)) (t,y) := by
  simp_rw [pinnedMetric_gradientPair g K hK hsa hu hv]
  have hf : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun z : ℝ × E => (chartAt E p).symm z.2) (t,y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy).comp (t,y)
      contDiffAt_snd.contMDiffAt
  have hk := (hK _).comp (t,y) hf
  have he := contMDiffAt_exp_along _ (contMDiffAt_smul_along _ hk
    (show ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ × E => z.1) (t,y) from
      contDiffAt_fst.contMDiffAt))
  have hu' := (contMDiff_metricGradient g hu _).comp (t,y) hf
  have hv' := (contMDiff_metricGradient g hv _).comp (t,y) hf
  have hh := ((g.contMDiff _).comp (t,y) hf).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    hu' (he.clm_bundle_apply hv')
  rw [contMDiffAt_totalSpace] at hh
  exact contMDiffAt_iff_contDiffAt.mp hh.2

lemma continuous_pinned_gradientPair :
    Continuous (fun z : ℝ × M => coordinateGradientPair (pinnedMetric g K hK z.1) u v z.2) := by
  apply continuous_joint_of_chart (E := E) (fun t x => coordinateGradientPair (pinnedMetric g K hK t) u v x)
  intro t p
  exact (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p))).continuousAt

lemma continuous_pinned_gradientPair_time_deriv :
    Continuous (fun z : ℝ × M => deriv
      (fun t => coordinateGradientPair (pinnedMetric g K hK t) u v z.2) z.1) := by
  apply continuous_joint_of_chart (E := E) (fun t x => deriv
    (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v x) t)
  intro t p
  exact (contDiffAt_partial_time_deriv (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p)))).continuousAt

lemma hasDerivAt_pinned_gradientPair_time (t : ℝ) (p : M) :
    HasDerivAt (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p)
      (deriv (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p) t) t := by
  have hh := (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p))).comp t
    (show ContDiffAt ℝ ∞ (fun r : ℝ => (r,chartAt E p p)) t from contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p) t := by
    simpa only [Function.comp_def,(chartAt E p).left_inv (mem_chart_source E p)] using hh
  exact (hf.differentiableAt (by simp)).hasDerivAt
end PinnedJointEnergy

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

lemma hasDerivAt_mean_family (f d : ℝ → M → ℝ)
    (hc : Continuous (fun z : ℝ × M => f z.1 z.2))
    (hd : Continuous (fun z : ℝ × M => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    HasDerivAt (fun t => I.mean g (f t)) (I.mean g (d 0)) 0 := by
  let F (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨f t,hc.comp (continuous_const.prodMk continuous_id)⟩
  let D (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨d t,hd.comp (continuous_const.prodMk continuous_id)⟩
  have hFD : HasDerivAt F (D 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa only [zero_add] using bounded_difference_quotient F D hd hf
  exact (I.integralCLM g).hasFDerivAt.comp_hasDerivAt 0 hFD

omit [CompactSpace M] [T2Space M] in
lemma mean_pinnedMetric (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (f : M → ℝ) : I.mean (pinnedMetric g K hK t) f = I.mean g f := by
  unfold mean
  apply Finset.sum_congr rfl
  intro i _
  unfold metricChartIntegral
  apply setIntegral_congr_fun (chartAt E (i:M)).open_target.measurableSet
  intro y hy
  dsimp only
  rw [pinnedMetric_det g K hK htr t (i:M) y hy]

theorem pinned_laplacian_first_variation
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x a b, g.inner x (K x a) b = g.inner x a (K x b))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) :
    I.mean g (fun x => u x * deriv (fun t => laplaceBeltrami (pinnedMetric g K hK t) v x) 0) =
      -I.mean g (fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x))) := by
  let q := pinnedMetric g K hK
  have hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y) := by
    intro p t y hy i j
    exact pinnedMetric_joint_coefficients g K hK p i j t hy
  have hL := I.hasDerivAt_mean_family g
    (fun t x => u x*laplaceBeltrami (q t) v x)
    (fun t x => u x*deriv (fun t => laplaceBeltrami (q t) v x) t)
    ((hu.continuous.comp continuous_snd).mul (continuous_joint_laplaceBeltrami q hq hv))
    ((hu.continuous.comp continuous_snd).mul (continuous_joint_laplaceBeltrami_time_deriv q hq hv))
    (fun t x => by simpa only [zero_mul,zero_add,Pi.mul_apply] using!
      (hasDerivAt_const t (u x)).mul (hasDerivAt_laplaceBeltrami_time q hq hv t x))
  have hE := I.hasDerivAt_mean_family g
    (fun t x => coordinateGradientPair (q t) u v x)
    (fun t x => deriv (fun t => coordinateGradientPair (q t) u v x) t)
    (continuous_pinned_gradientPair g K hK hsa hu hv)
    (continuous_pinned_gradientPair_time_deriv g K hK hsa hu hv)
    (hasDerivAt_pinned_gradientPair_time g K hK hsa hu hv)
  have he : (fun t => I.mean g (fun x => u x*laplaceBeltrami (q t) v x)) =
      fun t => -(I.mean g (coordinateGradientPair (q t) u v)) := by
    funext t
    rw [← I.mean_pinnedMetric g K hK htr t, I.green _ hu hv,I.mean_pinnedMetric g K hK htr t]
  rw [he] at hL
  have hdE : (fun x => deriv (fun t => coordinateGradientPair (q t) u v x) 0) =
      fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x)) := by
    funext x
    exact (pinnedMetric_gradientPair_deriv g K hK hsa hu hv x).deriv
  rw [hdE] at hE
  exact hL.unique hE.neg
end MetricIntegralAtlas

end YauCounterexamples
end

end OAI
