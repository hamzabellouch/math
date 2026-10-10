import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma isGeodesic_zero (x : M) : IsGeodesicWithInitialData (n := n) x 0 (fun _ => x) := by
  refine ⟨contMDiff_const, ?_, ?_⟩
  · simp only [mfderiv_const]
    rfl
  · intro t
    refine ⟨1, by norm_num, ?_⟩
    intro s u _ _
    simp

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma geodesic_initial_point {x : M} {v : TangentSpace 𝓘(ℝ, Model n) x}
    {gamma : ℝ → M} (h : IsGeodesicWithInitialData x v gamma) : gamma 0 = x := by
  exact congrArg (fun p : TangentBundle 𝓘(ℝ, Model n) M => p.proj) h.2.1

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in

lemma geodesic_zero_eq_const {x : M} {gamma : ℝ → M}
    (h : IsGeodesicWithInitialData (n := n) x 0 gamma) : gamma = fun _ => x := by
  have hl : IsLocallyConstant gamma := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨eps, heps, hh⟩ := h.2.2 t
    refine ⟨Metric.ball t eps, Metric.isOpen_ball, Metric.mem_ball_self heps, ?_⟩
    intro s hs
    apply dist_eq_zero.mp
    simpa only [norm_zero, mul_zero] using
      hh s t (by simpa only [Metric.mem_ball, Real.dist_eq] using hs) (by simpa using heps)
  funext t
  exact (hl.apply_eq_of_preconnectedSpace t 0).trans (geodesic_initial_point h)

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
@[simp] lemma riemannianExp_zero (x : M) : riemannianExp (n := n) x 0 = x := by
  have hex : ∃ gamma, IsGeodesicWithInitialData (n := n) x 0 gamma := ⟨_, isGeodesic_zero (n := n) x⟩
  rw [riemannianExp, dite_eq_left hex]
  exact congrFun (geodesic_zero_eq_const (Classical.choose_spec hex)) 1

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma zero_mem_injectivityDomain (x : M) : (0 : TangentSpace 𝓘(ℝ, Model n) x) ∈ injectivityDomain x := by
  refine ⟨2, by norm_num, ?_⟩
  simp

end WeakMTWTransport
end

end OAI
