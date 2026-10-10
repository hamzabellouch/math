import Mathlib
import OAI.Geometry.SmoothYau.Estimates.VaryingPatchCoefficients
import OAI.Geometry.SmoothYau.Smoothness.ChartDerivativeNeZeroTransfer

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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs) (q : SmoothMetric E M)

omit [T2Space M] in
lemma varyingLaplacian_mem_realH (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    A.varyingLaplacianCLM q B u ∈ A.realH (2 * (k : ℝ)) := by
  intro x
  rw [A.varyingLaplacianCLM_representative]
  change laplaceBeltrami q (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x = 0
  have he : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u : M → ℝ) = fun _ => 0 :=
    funext u.property
  rw [he, laplaceBeltrami_zero]

def varyingRealLaplacian (B : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.varyingLaplacianCLM q B |>.restrict fun u hu => A.varyingLaplacian_mem_realH q B ⟨u,hu⟩

omit [T2Space M] in
lemma varyingRealLaplacian_value (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingRealLaplacian q B u) x =
      laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  change (A.representative _ (A.varyingLaplacianCLM q B u) x).re = _
  rw [A.varyingLaplacianCLM_representative]
  rfl

def varyingShift (B : ∀ i, A.VaryingPatchCoefficients q i) (α : ℝ) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  α • A.realInclusion - A.varyingRealLaplacian q B

omit [T2Space M] in
lemma varyingShift_value (B : ∀ i, A.VaryingPatchCoefficients q i) (α : ℝ)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingShift q B α u) x =
      α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x -
        laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [varyingShift, sub_apply, smul_apply,
    A.realValue_sub, A.realValue_smul, A.realValue_inclusion, A.varyingRealLaplacian_value]

omit [T2Space M] in
lemma varyingRealLaplacian_independent (B C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.varyingRealLaplacian q B = A.varyingRealLaplacian q C := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply manifoldSobolevRepresentative_injective A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η hs
  ext x
  change A.representative _ (A.varyingLaplacianCLM q B u) x =
    A.representative _ (A.varyingLaplacianCLM q C u) x
  rw [A.varyingLaplacianCLM_representative, A.varyingLaplacianCLM_representative]
end CompactMetricAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold BoundedContinuousFunction SchwartzMap
section CoefficientOperatorContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma coefficientPerturbation_tendsto_at {ι P : Type*} [Fintype ι] {l : Filter P}
    (b : ι → E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (a : P → ι → ι → FourierSobolevSpace E ℂ s) (c : P → ι → FourierSobolevSpace E ℂ s)
    (a₀ : ι → ι → FourierSobolevSpace E ℂ s) (c₀ : ι → FourierSobolevSpace E ℂ s)
    (ha : ∀ i j, Tendsto (fun p => a p i j) l (𝓝 (a₀ i j)))
    (hc : ∀ i, Tendsto (fun p => c p i) l (𝓝 (c₀ i))) :
    Tendsto (fun p => coefficientPerturbation b hs (a p) (c p)) l
      (𝓝 (coefficientPerturbation b hs a₀ c₀)) := by
  have hmul {f : P → FourierSobolevSpace E ℂ s} {f₀ : FourierSobolevSpace E ℂ s}
      (hf : Tendsto f l (𝓝 f₀))
      (D : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s) :
      Tendsto (fun p => (sobolevProduct hs (f p)) ∘L D) l
        (𝓝 ((sobolevProduct hs f₀) ∘L D)) := by
    have hh : Continuous (fun v : FourierSobolevSpace E ℂ s => (sobolevProduct hs v) ∘L D) := by
      fun_prop
    exact hh.continuousAt.tendsto.comp hf
  exact (tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hmul (ha i j) _))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hmul (hc i) _))
end CoefficientOperatorContinuity
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

@[reducible] local instance H_nacg (s : ℝ) : NormedAddCommGroup (A.H s) := inferInstance
@[reducible] local instance H_ns (s : ℝ) : NormedSpace ℝ (A.H s) := inferInstance

omit [T2Space M] in

theorem varyingLaplacianCLM_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (ha : ∀ i j m, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).a j m) ((C p i).smooth_a j m))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).a j m) ((C₀ i).smooth_a j m)))))
    (hc : ∀ i j, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).c j) ((C p i).smooth_c j))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).c j) ((C₀ i).smooth_c j))))) :
    Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀)) := by
  apply tendsto_finsetSum Finset.univ
  intro i _
  have hpert := coefficientPerturbation_tendsto_at (Module.finBasis ℝ E) hs _ _ _ _ (ha i) (hc i)
  have hres : Continuous (fun D : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) => D.restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).continuous
  have hout : Continuous (fun D : FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) =>
      A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L D ∘L
        A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)) := by
    fun_prop
  exact hout.continuousAt.tendsto.comp (hres.continuousAt.tendsto.comp hpert)

omit [T2Space M] in
lemma varyingRealLaplacian_norm_sub_le (q q₀ : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) :
    ‖A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀‖ ≤
      ‖A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀) (norm_nonneg _)
  intro v
  exact (A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀).le_opNorm v.val

omit [T2Space M] in
lemma varyingRealLaplacian_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingRealLaplacian (q p) (C p)) l
      (𝓝 (A.varyingRealLaplacian q₀ C₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun p =>
    A.varyingRealLaplacian_norm_sub_le (q p) q₀ (C p) C₀) h

omit [T2Space M] in
lemma varyingShift_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) (α : ℝ)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift q₀ C₀ α)) :=
  tendsto_const_nhds.sub (A.varyingRealLaplacian_tendsto q q₀ C C₀ h)
end CompactMetricAtlas


end YauCounterexamples
end

end OAI
