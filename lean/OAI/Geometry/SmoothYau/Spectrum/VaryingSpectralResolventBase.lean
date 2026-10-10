import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.TransferAcross
import OAI.Geometry.SmoothYau.Estimates.PreconditionedInverse
import OAI.Geometry.SmoothYau.Geometry.PinnedMetricJointGradientPair
import OAI.Geometry.SmoothYau.Smoothness.PinningTensorSpace
import OAI.Geometry.SmoothYau.Spectrum.ContinuousEigenpairLinearization
import OAI.Geometry.SmoothYau.Spectrum.CompactPerturbedEigenvectors
import OAI.Geometry.SmoothYau.Spectrum.TransverseZeroKernel

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
variable (A : CompactMetricAtlas g k hs)

lemma varyingShift_base_comp_resolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingShift g C α ∘L A.realResolvent B α hα0 hα he = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply A.realRepresentative_injective _ hs
  ext x
  change A.realValue _ (A.varyingShift g C α (A.realResolvent B α hα0 hα he u)) x = _
  rw [A.varyingShift_value]
  exact A.realResolvent_value B α hα0 hα he u x

def varyingResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * ((k + 1 : ℕ) : ℝ)) :=
  preconditionedInverse (A.realResolvent B α hα0 hα he) (A.varyingShift q C α)

lemma varyingResolvent_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i)
    (hunit : IsUnit (A.varyingShift q C α ∘L A.realResolvent B α hα0 hα he))
    (u : A.realH (2 * (k : ℝ))) (x : M) :
    α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (A.varyingResolvent B α hα0 hα he q C u) x -
      laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ))
        (A.varyingResolvent B α hα0 hα he q C u)) x = A.realValue (2 * (k : ℝ)) u x := by
  have hcomp : A.varyingShift q C α ∘L A.varyingResolvent B α hα0 hα he q C = 1 :=
    preconditionedInverse_right (A.realResolvent B α hα0 hα he) (A.varyingShift q C α) hunit
  have hu : A.varyingShift q C α (A.varyingResolvent B α hα0 hα he q C u) = u :=
    DFunLike.congr_fun hcomp u
  have hv := congrArg (fun v : A.realH (2 * (k : ℝ)) => A.realValue (2 * (k : ℝ)) v x) hu
  rwa [A.varyingShift_value] at hv

lemma varyingResolvent_base (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingResolvent B α hα0 hα he g C = A.realResolvent B α hα0 hα he :=
  preconditionedInverse_base _ _ (A.varyingShift_base_comp_resolvent B α hα0 hα he C)

def varyingSpectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.realInclusion ∘L A.varyingResolvent B α hα0 hα he q C

lemma varyingSpectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) :
    IsCompactOperator (A.varyingSpectralResolvent B α hα0 hα he q C) :=
  (A.realSpectralResolvent_compact B α hα0 hα he).comp_clm
    (Ring.inverse (A.varyingShift q C α ∘L A.realResolvent B α hα0 hα he))

theorem varyingResolvent_tendsto {P : Type*} {l : Filter P}
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C₀ : ∀ i, A.VaryingPatchCoefficients g i)
    (q : P → SmoothMetric E M) (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (hC : Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift g C₀ α))) :
    (∀ᶠ p in l, IsUnit (A.varyingShift (q p) (C p) α ∘L A.realResolvent B α hα0 hα he)) ∧
      Tendsto (fun p => A.varyingResolvent B α hα0 hα he (q p) (C p)) l
        (𝓝 (A.realResolvent B α hα0 hα he)) := by
  have hb := A.varyingShift_base_comp_resolvent B α hα0 hα he C₀
  exact ⟨hC.eventually (eventuallyIsUnit_preconditioned _ _ (hb ▸ isUnit_one)),
    preconditionedInverse_tendsto _ _ hb _ hC⟩
end CompactMetricAtlas

end

section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma laplaceBeltrami_const_mul_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) (c : ℝ) (x : M) :
    laplaceBeltrami g (fun y => c*u y) x = c*laplaceBeltrami g u x := by
  have h := complexLaplaceBeltrami_const_mul (Complex.ofRealCLM.contMDiff.comp hu) (c : ℂ) g x
  change complexLaplaceBeltrami g (fun y => (c : ℂ)*(u y : ℂ)) x =
    (c : ℂ)*complexLaplaceBeltrami g (fun y => (u y : ℂ)) x at h
  have he : (fun y => (c : ℂ)*(u y : ℂ)) = fun y => ((c*u y : ℝ) : ℂ) := by ext y; simp
  rw [he,complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal] at h
  exact_mod_cast h

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem represented_eigenfunction_smooth (q : SmoothMetric E M) (lam : ℝ)
    (v : A.realH (2*((k+1:ℕ):ℝ)))
    (he : ∀ x, -laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) v) x =
      lam*A.realValue (2*((k+1:ℕ):ℝ)) v x) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) v) := by
  let B := (nonempty_compactMetricAtlas q k hs).some
  have ht : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)) := by push_cast; linarith
  let u := A.realValue (2*((k+1:ℕ):ℝ)) v
  let w := A.transferAcross B (k+1) v
  have hw : (B.representative (2*((k+1:ℕ):ℝ)) w : M → ℂ) = fun x => (u x : ℂ) := by
    rw [show w = A.transferAcross B (k+1) v from rfl,A.transferAcross_representative B (k+1) ht]
    ext x
    exact (A.ofReal_realValue _ v x).symm
  let a : Fin 2 → ManifoldSmoothFunctions E M := fun i =>
    if i=1 then ⟨fun _ => (-lam : ℝ),contMDiff_const⟩ else 0
  have he' (x : M) : complexLaplaceBeltrami q (fun x => (u x : ℂ)) x =
      ∑ i, a i x*(u x : ℂ)^i.val := by
    rw [complexLaplaceBeltrami_ofReal]
    have hx : laplaceBeltrami q u x = -lam*u x := by linarith [he x]
    rw [hx]
    simp [a,Fin.sum_univ_succ,Fin.ext_iff]
  have hh := B.represented_semilinear_solution_smooth a
    (Complex.ofRealCLM.contMDiff.comp (A.realValue_C2 v)) he' w hw
  have hh' := Complex.reCLM.contMDiff.comp hh
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.ofRealCLM_apply,Complex.ofReal_re] using hh'

theorem shiftedInverse_eigenfunction (q : SmoothMetric E M) (α : ℝ)
    (R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)))
    (hR : ∀ z x, α*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x -
      laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x = A.realValue (2*(k:ℝ)) z x)
    {μ : ℝ} (hμ : μ ≠ 0) (z : A.realH (2*(k:ℝ)))
    (hz : A.realInclusion (R z) = μ • z) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) z) ∧
    (∀ x, -laplaceBeltrami q (A.realValue (2*(k:ℝ)) z) x =
      (μ⁻¹-α)*A.realValue (2*(k:ℝ)) z x) := by
  let w := μ⁻¹ • R z
  have hw (x : M) : A.realValue (2*((k+1:ℕ):ℝ)) w x = A.realValue (2*(k:ℝ)) z x := by
    rw [show w = μ⁻¹ • R z from rfl,A.realValue_smul,← A.realValue_inclusion,hz,A.realValue_smul]
    rw [← mul_assoc,inv_mul_cancel₀ hμ,one_mul]
  have hew (x : M) : -laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) w) x =
      (μ⁻¹-α)*A.realValue (2*((k+1:ℕ):ℝ)) w x := by
    have hv : A.realValue (2*((k+1:ℕ):ℝ)) w =
        fun x => μ⁻¹*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x := funext (A.realValue_smul _ _ _)
    rw [hv,laplaceBeltrami_const_mul_C2 q (A.realValue_C2 _) μ⁻¹]
    have hval : A.realValue (2*((k+1:ℕ):ℝ)) (R z) x = μ*A.realValue (2*(k:ℝ)) z x := by
      rw [← A.realValue_inclusion,hz,A.realValue_smul]
    have hinv := inv_mul_cancel₀ hμ
    have hr := hR z x
    rw [hval] at hr
    dsimp only
    rw [hval]
    have heq : laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x =
        α*μ*A.realValue (2*(k:ℝ)) z x - A.realValue (2*(k:ℝ)) z x := by linarith
    rw [heq]
    field_simp
    ring
  rw [funext hw] at hew
  exact ⟨(funext hw) ▸ A.represented_eigenfunction_smooth q (μ⁻¹-α) w (by simpa only [funext hw] using hew),hew⟩

theorem realSpectralResolvent_eigenfunction
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    {μ : ℝ} (hμ : μ ≠ 0) (z : A.realH (2*(k:ℝ)))
    (hz : A.realSpectralResolvent B α hα0 hα he z = μ • z) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) z) ∧
    (∀ x, -laplaceBeltrami g (A.realValue (2*(k:ℝ)) z) x =
      (μ⁻¹-α)*A.realValue (2*(k:ℝ)) z x) :=
  A.shiftedInverse_eigenfunction g α (A.realResolvent B α hα0 hα he)
    (A.realResolvent_value B α hα0 hα he) hμ z hz

end CompactMetricAtlas
end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [T2Space M] in
lemma eigen_mean_laplace_difference (q : SmoothMetric E M)
    (hm : ∀ f, I.mean q f = I.mean g f)
    {a z : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)
    (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ z) (lam : ℝ)
    (hea : ∀ x, -laplaceBeltrami g a x = lam*a x)
    (hez : ∀ x, -laplaceBeltrami q z x = lam*z x) :
    I.mean g (fun x => z x*(laplaceBeltrami q a x-laplaceBeltrami g a x)) = 0 := by
  have hsym := I.laplacian_symmetric_C2 q (hz.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [hm,hm] at hsym
  have he : (fun x => laplaceBeltrami q z x*a x) = fun x => z x*laplaceBeltrami g a x := by
    funext x
    have h1 := hea x
    have h2 := hez x
    have h1' : laplaceBeltrami g a x = -lam*a x := by linarith
    have h2' : laplaceBeltrami q z x = -lam*z x := by linarith
    rw [h1',h2']; ring
  rw [he] at hsym
  simp_rw [mul_sub]
  calc
    _ = I.mean g (fun x => z x*laplaceBeltrami q a x) -
        I.mean g (fun x => z x*laplaceBeltrami g a x) :=
      I.mean_sub g _ _ (hz.continuous.mul (contMDiff_laplaceBeltrami ha q).continuous)
        (hz.continuous.mul (contMDiff_laplaceBeltrami ha g).continuous)
    _ = 0 := sub_eq_zero.mpr hsym
end MetricIntegralAtlas
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

def scalarTestCLM (s : ℝ) : (M →ᵇ ℝ) →L[ℝ] A.realH s →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (A.realH s) (M →ᵇ ℝ) ℝ (I.integralCLM g) ∘L
    (ContinuousLinearMap.mul ℝ (M →ᵇ ℝ)).bilinearComp
      (ContinuousLinearMap.id ℝ (M →ᵇ ℝ)) (A.realRepresentative s)

omit [T2Space M] in
lemma scalarTestCLM_apply (s : ℝ) (f : M →ᵇ ℝ) (z : A.realH s) :
    A.scalarTestCLM I s f z = I.mean g (fun x => f x*A.realValue s z x) := rfl
end CompactMetricAtlas

variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)

def laplaceFamilyBCF (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
  ⟨laplaceBeltrami (q t) a,(continuous_joint_laplaceBeltrami q hq ha).comp
    (continuous_const.prodMk continuous_id)⟩
def laplaceDerivativeBCF (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
  ⟨fun x => deriv (fun r => laplaceBeltrami (q r) a x) t,
    by
      have hh := (continuous_joint_laplaceBeltrami_time_deriv q hq ha).comp
        (show Continuous (fun x : M => (t,x)) from continuous_const.prodMk continuous_id)
      simpa only [Function.comp_def] using hh⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplaceFamilyBCF_first_quotient :
    Tendsto (fun t => t⁻¹ • (laplaceFamilyBCF q hq ha t-laplaceFamilyBCF q hq ha 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 (laplaceDerivativeBCF q hq ha 0)) :=
  bounded_difference_quotient _ _ (continuous_joint_laplaceBeltrami_time_deriv q hq ha)
    (hasDerivAt_laplaceBeltrami_time q hq ha)

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

def laplaceVariationTest (s t : ℝ) : A.realH s →L[ℝ] ℝ :=
  A.scalarTestCLM I s (t⁻¹ • (laplaceFamilyBCF q hq ha t-laplaceFamilyBCF q hq ha 0))

lemma laplaceVariationTest_limit (s : ℝ) :
    Tendsto (A.laplaceVariationTest q hq ha I s) (𝓝[≠] (0 : ℝ))
      (𝓝 (A.scalarTestCLM I s (laplaceDerivativeBCF q hq ha 0))) :=
  (A.scalarTestCLM I s).continuous.tendsto _ |>.comp
    (laplaceFamilyBCF_first_quotient q hq ha)

omit [T2Space M] in
lemma laplaceVariationTest_eigen_zero (s t : ℝ)
    (hbase : q 0 = g) (hm : ∀ f, I.mean (q t) f = I.mean g f)
    (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z))
    (lam : ℝ) (hea : ∀ x, -laplaceBeltrami g a x = lam*a x)
    (hez : ∀ x, -laplaceBeltrami (q t) (A.realValue s z) x = lam*A.realValue s z x) :
    A.laplaceVariationTest q hq ha I s t z = 0 := by
  unfold laplaceVariationTest
  rw [map_smul,smul_apply,smul_eq_mul]
  have hh := I.eigen_mean_laplace_difference g (q t) hm ha hz lam hea hez
  have he : A.scalarTestCLM I s (laplaceFamilyBCF q hq ha t-laplaceFamilyBCF q hq ha 0) z = 0 := by
    rw [A.scalarTestCLM_apply]
    convert hh using 2
    funext x
    change (laplaceBeltrami (q t) a x-laplaceBeltrami (q 0) a x)*A.realValue s z x = _
    rw [hbase,mul_comm]
  rw [he,mul_zero]
end CompactMetricAtlas
end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
omit [MeasurableSpace E] [BorelSpace E] [T2Space M] in
lemma real_positive_shift_solution_unique (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (he : ∀ x, α*u x-laplaceBeltrami g u x = α*v x-laplaceBeltrami g v x) : u = v := by
  have hh : (fun x => (u x : ℂ)) = fun x => (v x : ℂ) :=
    complex_positive_shift_solution_unique g hα (Complex.ofRealCLM.contMDiff.comp hu)
      (Complex.ofRealCLM.contMDiff.comp hv) (by
        intro x
        rw [complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal]
        exact_mod_cast he x)
  funext x
  exact Complex.ofReal_injective (congrFun hh x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma smoothMetric_eq_of_inner_eq (g h : SmoothMetric E M) (he : g.inner = h.inner) : g = h := by
  cases g
  cases h
  cases he
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma pinnedMetric_at_zero (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) : pinnedMetric g K hK 0 = g := by
  have hh : (pinnedMetric g K hK 0).inner = g.inner := by
    funext x
    ext a b
    simp only [pinnedMetric_inner, neg_zero, zero_div]
    erw [zero_smul, NormedSpace.exp_zero]
    rfl
  exact smoothMetric_eq_of_inner_eq _ _ hh

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem shiftedInverse_of_smooth_eigenfunction (q : SmoothMetric E M) (α : ℝ) (hα : 0 < α)
    (R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)))
    (hR : ∀ z x, α*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x -
      laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x = A.realValue (2*(k:ℝ)) z x)
    (lam : ℝ) (hn : α+lam ≠ 0) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (he : ∀ x, -laplaceBeltrami q u x = lam*u x) :
    A.realInclusion (R (A.realOfSmooth (2*(k:ℝ)) hs u hu)) =
      (α+lam)⁻¹ • A.realOfSmooth (2*(k:ℝ)) hs u hu := by
  let z := A.realOfSmooth (2*(k:ℝ)) hs u hu
  have hv : A.realValue (2*((k+1:ℕ):ℝ)) (R z) = fun x => (α+lam)⁻¹*u x := by
    apply real_positive_shift_solution_unique q hα (A.realValue_C2 (R z))
      (contMDiff_const.mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
    intro x
    rw [hR,A.realOfSmooth_value]
    change u x = α*((α+lam)⁻¹*u x)-laplaceBeltrami q (fun y => (α+lam)⁻¹*u y) x
    rw [laplaceBeltrami_const_mul_C2 q
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    have hx : laplaceBeltrami q u x = -lam*u x := by linarith [he x]
    rw [hx]
    field_simp
    ring
  apply A.realRepresentative_injective (2*(k:ℝ)) hs
  ext x
  change A.realValue _ (A.realInclusion (R z)) x = A.realValue _ ((α+lam)⁻¹ • z) x
  rw [A.realValue_inclusion,A.realValue_smul,A.realOfSmooth_value]
  exact congrFun hv x

def realSmoothRepresentativeLM (s : ℝ) (P : Submodule ℝ (A.realH s))
    (hf : ∀ w : P, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s w)) :
    P →ₗ[ℝ] RealSmoothFunctions E M where
  toFun w := ⟨A.realValue s w,hf w⟩
  map_add' a b := by
    ext x
    exact A.realValue_add s a b x
  map_smul' r a := by
    ext x
    exact A.realValue_smul s r a x

omit [T2Space M] in
lemma realSmoothRepresentativeLM_injective (s : ℝ) (ht : Module.finrank ℝ E < 2*s)
    (P : Submodule ℝ (A.realH s))
    (hf : ∀ w : P, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s w)) :
    Injective (A.realSmoothRepresentativeLM s P hf) := by
  intro a b hab
  apply Subtype.ext
  apply A.realRepresentative_injective s ht
  ext x
  exact DFunLike.congr_fun hab x

theorem smoothFamily_resolvent_tendsto
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (q : ℝ → SmoothMetric E M) (hq0 : q 0 = g)
    (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
    (∀ᶠ t in 𝓝 (0:ℝ), IsUnit (A.varyingShift (q t) (C t) α ∘L A.realResolvent B α hα0 hα he)) ∧
    Tendsto (fun t => A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)) (𝓝 (0:ℝ))
      (𝓝 (A.realSpectralResolvent B α hα0 hα he)) := by
  let C₀ : ∀ i, A.VaryingPatchCoefficients g i := hq0 ▸ C 0
  have hc := A.smoothFamily_varyingLaplacian_tendsto q hq C
  have hbase : A.varyingLaplacianCLM (q 0) (C 0) = A.varyingLaplacianCLM g C₀ := by
    subst g
    rfl
  rw [hbase] at hc
  obtain ⟨hunit,hlim⟩ := A.varyingResolvent_tendsto B α hα0 hα he C₀ q C
    (A.varyingShift_tendsto q g C C₀ α hc)
  have hcont : Continuous (fun R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)) =>
      A.realInclusion ∘L R) := by fun_prop
  exact ⟨hunit,hcont.tendsto _ |>.comp hlim⟩
end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
lemma varyingSpectralResolvent_base
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingSpectralResolvent B α hα0 hα he g C = A.realSpectralResolvent B α hα0 hα he := by
  unfold varyingSpectralResolvent realSpectralResolvent
  rw [A.varyingResolvent_base]

lemma varyingSpectralResolvent_eq_base
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (q : SmoothMetric E M) (hq : q = g) (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.varyingSpectralResolvent B α hα0 hα he q C = A.realSpectralResolvent B α hα0 hα he := by
  subst q
  exact A.varyingSpectralResolvent_base B α hα0 hα he C

lemma scalarTestCLM_pinned_deriv (I : MetricIntegralAtlas (E := E) (M := M))
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)
    (s : ℝ) (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z)) :
    A.scalarTestCLM I s (laplaceDerivativeBCF (pinnedMetric g K.val K.property.1)
      (fun p t _ hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy) ha 0) z =
      -I.mean g (fun x => g.inner x (metricGradient g (A.realValue s z) x)
        (K.val x (metricGradient g a x))) := by
  have hh := I.pinned_laplacian_first_variation g K.val K.property.1 K.property.2.1
    K.property.2.2.1 hz ha
  change I.mean g (fun x => deriv (fun t => laplaceBeltrami (pinnedMetric g K.val K.property.1 t) a x) 0*
    A.realValue s z x) = _
  convert hh using 2
  funext x
  exact mul_comm _ _

theorem actual_pinned_eventually_simple
    (I : MetricIntegralAtlas (E := E) (M := M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    {U : Set M} (K : pinningTensorSpace g u U)
    (hnd : ∀ z : A.realH (2*(k:ℝ)),
      A.realSpectralResolvent B α hα0 hα he z = (α+lam)⁻¹ • z →
      I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) = 0 →
      (∀ a : A.realH (2*(k:ℝ)),
        A.realSpectralResolvent B α hα0 hα he a = (α+lam)⁻¹ • a →
        I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) a x) = 0 →
        I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(k:ℝ)) z) x)
          (K.val x (metricGradient g (A.realValue (2*(k:ℝ)) a) x))) = 0) → z = 0) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x = lam*v x) →
      ∃ c : ℝ, v = fun x => c*u x := by
  classical
  let q := pinnedMetric g K.val K.property.1
  have hq0 : q 0 = g := pinnedMetric_at_zero g K.val K.property.1
  have hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y) :=
    fun p t y hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy
  let C : ∀ t i, A.VaryingPatchCoefficients (q t) i := fun t i =>
    (A.nonempty_varyingPatchCoefficients (q t) i).some
  let T (t : ℝ) := A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)
  let T₀ := A.realSpectralResolvent B α hα0 hα he
  have hT0 : T 0 = T₀ := by
    dsimp only [T,T₀]
    exact A.varyingSpectralResolvent_eq_base B α hα0 hα he (q 0) hq0 (C 0)
  obtain ⟨hunit,hlim⟩ := A.smoothFamily_resolvent_tendsto B α hα0 hα he q hq0
    (fun i => hq (A.p i)) C
  have hT : Tendsto T (𝓝 (0:ℝ)) (𝓝 (T 0)) := hT0.symm ▸ hlim
  let μ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hn
  have hμv : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let uz := A.realOfSmooth (2*(k:ℝ)) hs u hu
  have huz : uz ≠ 0 := by
    intro hz
    apply hu0
    funext x
    have hh := congrArg (fun z => A.realValue (2*(k:ℝ)) z x) hz
    have hzv : A.realValue (2*(k:ℝ)) 0 x = 0 := by
      simpa only [zero_smul,zero_mul] using A.realValue_smul (2*(k:ℝ)) 0 uz x
    simpa only [uz,A.realOfSmooth_value,hzv,Pi.zero_apply] using hh
  have hbase (a : A.realH (2*(k:ℝ))) (ha : T₀ a = μ • a) :
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) a) ∧
      ∀ x, -laplaceBeltrami g (A.realValue (2*(k:ℝ)) a) x = lam*A.realValue (2*(k:ℝ)) a x := by
    have hh := A.realSpectralResolvent_eigenfunction B α hα0 hα he hμ a ha
    simpa only [hμv] using hh
  let sa (a : A.realH (2*(k:ℝ))) : RealSmoothFunctions E M :=
    if ha : T₀ a = μ • a then ⟨A.realValue (2*(k:ℝ)) a,(hbase a ha).1⟩ else 0
  have hsa (a : A.realH (2*(k:ℝ))) (ha : T₀ a = μ • a) :
      (sa a : M → ℝ) = A.realValue (2*(k:ℝ)) a := by
    have hh : sa a = ⟨A.realValue (2*(k:ℝ)) a, (hbase a ha).1⟩ := dite_eq_left ha
    exact congrArg (fun f : RealSmoothFunctions E M => (f : M → ℝ)) hh
  let test (a : A.realH (2*(k:ℝ))) := A.laplaceVariationTest q hq (sa a).contMDiff I (2*(k:ℝ))
  let test₀ (a : A.realH (2*(k:ℝ))) := A.scalarTestCLM I (2*(k:ℝ))
    (laplaceDerivativeBCF q hq (sa a).contMDiff 0)
  let P := A.intrinsicPairing I (2*(k:ℝ)) hs
  have hp (z : A.realH (2*(k:ℝ))) :
      P.form uz z = I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) := by
    change I.mean g (fun x => A.realValue (2*(k:ℝ)) uz x*A.realValue (2*(k:ℝ)) z x) = _
    congr 1
    funext x
    rw [A.realOfSmooth_value]
  have hueT : ∀ᶠ t in 𝓝[≠] (0:ℝ), T t uz = μ • uz := by
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht
    exact A.shiftedInverse_of_smooth_eigenfunction (q t) α hα0
      (A.varyingResolvent B α hα0 hα he (q t) (C t))
      (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) ht) lam hn u hu
      (fun x => (congrArg Neg.neg (pinnedMetric_laplacian g K.val K.property.1
        K.property.2.1 K.property.2.2.1 hu K.property.2.2.2.1 t x)).trans (hue x))
  have hvan : ∀ a, T 0 a = μ • a → ∀ᶠ t in 𝓝[≠] (0:ℝ),
      ∀ z, T t z = μ • z → test a t z = 0 := by
    intro a ha
    have ha' : T₀ a = μ • a := hT0 ▸ ha
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht z hz
    have hzz := A.shiftedInverse_eigenfunction (q t) α
      (A.varyingResolvent B α hα0 hα he (q t) (C t))
      (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) ht) hμ z hz
    rw [hμv] at hzz
    exact A.laplaceVariationTest_eigen_zero q hq (sa a).contMDiff I (2*(k:ℝ)) t hq0
      (I.mean_pinnedMetric g K.val K.property.1 K.property.2.2.1 t) z hzz.1 lam
      (by rw [hsa a ha']; exact (hbase a ha').2) hzz.2
  have hpin := P.pinned_weak_first_variation T test test₀
    (hT0.symm ▸ A.realSpectralResolvent_compact B α hα0 hα he) hT hμ huz hueT
    (fun a _ => A.laplaceVariationTest_limit q hq (sa a).contMDiff I (2*(k:ℝ))) hvan
    (by
      intro z hz hzp hab
      have hz' : T₀ z = μ • z := hT0 ▸ hz
      apply hnd z hz' ((hp z) ▸ hzp)
      intro a ha hap
      have hh := hab a (hT0.symm ▸ ha) ((hp a).symm ▸ hap)
      have heq := A.scalarTestCLM_pinned_deriv I K (sa a).contMDiff (2*(k:ℝ)) z (hbase z hz').1
      change test₀ a z = _ at heq
      rw [heq,hsa a ha] at hh
      exact neg_eq_zero.mp hh)
  filter_upwards [hpin,hunit.filter_mono nhdsWithin_le_nhds] with t ht hi v hv hve
  let vz := A.realOfSmooth (2*(k:ℝ)) hs v hv
  have hveT : T t vz = μ • vz := A.shiftedInverse_of_smooth_eigenfunction (q t) α hα0
    (A.varyingResolvent B α hα0 hα he (q t) (C t))
    (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) hi) lam hn v hv hve
  obtain ⟨c,hc⟩ := ht vz hveT
  refine ⟨c,?_⟩
  funext x
  have hh := congrArg (fun z => A.realValue (2*(k:ℝ)) z x) hc
  simpa only [vz,uz,A.realValue_smul,A.realOfSmooth_value] using hh
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
