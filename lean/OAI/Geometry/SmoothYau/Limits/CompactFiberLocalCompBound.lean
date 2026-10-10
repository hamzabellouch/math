import Mathlib
import OAI.Geometry.SmoothYau.Estimates.NormalFamilyInverseExtension
import OAI.Geometry.SmoothYau.Smoothness.FamilyInverseFst
import OAI.Geometry.SmoothYau.Smoothness.UniformJetBoundsFiberComp

namespace OAI

noncomputable section
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section LocalCompTransfer
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_fiber_local_comp_bound (ψ : P × E → F) (hψ : ContDiff ℝ ∞ ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ C > 0, ∀ q : P, ∀ u : E → V, ∀ f : F → V, ContDiff ℝ ∞ f →
      (∀ y ∈ tsupport u, (q,y) ∈ L ∧ u =ᶠ[𝓝 y] (fun z => f (ψ (q,z)))) →
      ∀ n : ℝ, 1 ≤ n → ∀ a : E → ℝ, (∀ y, 0 ≤ a y) →
      (∀ y ∈ tsupport u, ∀ i ≤ m,
        ‖iteratedFDeriv ℝ i f (ψ (q,y))‖ ≤ a y*n^i) →
      ∀ y, ∀ k ≤ m, ‖iteratedFDeriv ℝ k u y‖ ≤ C*a y*n^k := by
  obtain ⟨C,hC,hb⟩ := compact_fiber_comp_derivative_bound ψ hψ hL m (V := V)
  refine ⟨C,hC,?_⟩
  intro q u f hf hu n hn a ha he y k hk
  by_cases hy : y ∈ tsupport u
  · obtain ⟨hyL,hug⟩ := hu y hy
    rw [(hug.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hb (q,y) hyL f hf n hn (a y) (ha y) (he y hy) k hk
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hy
    rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg (mul_nonneg hC.le (ha y)) (pow_nonneg (le_trans zero_le_one hn) _)
end LocalCompTransfer

theorem exists_normal_wave_chart_family (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∃ e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace,
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
      (∀ q, ContDiffOn ℝ ∞ (e q).symm (e q).target) ∧
      (∀ q ∈ metricFrameSet g K, Metric.closedBall (0 : NormalWaveSpace) r ⊆ (e q).source) ∧
      ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace, ContDiff ℝ ∞ ψ ∧
        ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : NormalWaveSpace) r,
          (e q).symm =ᶠ[𝓝 (e q x)] (fun y => ψ (q,y)) := by
  obtain ⟨r,hr,e,he,hs,hi,hR,ψ,hψ,hg⟩ := normal_family_inverse_extension g hK
  have he1 : ∀ w, (e w).1 = w.1 := by intro w; rw [he]; rfl
  let eq := fiberOpenPartialHomeomorph e he1
  have heq (q : NormalWaveParameter) : (eq q : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) := by
    funext x
    change (e (q,x)).2 = _
    rw [he]
    rfl
  refine ⟨r,hr,eq,heq,(fun q => contDiffOn_fiberInverse e he1 q hi),?_,ψ,hψ,?_⟩
  · intro q hq x hx
    exact hR q hq x hx
  · intro q hq x hx
    change (fun y => (e.symm (q,y)).2) =ᶠ[𝓝 (eq q x)] (fun y => ψ (q,y))
    rw [heq]
    exact hg q hq x hx
end YauCounterexamples

end

end OAI
