import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteGNSNormality
import OAI.Analysis.BoundedHochschild.NormalVectors

namespace OAI

/-! A positive trace normal for a Banach predual has normal native GNS
range. Bounded predual compactness and cyclic coefficients close the GNS
trace-vector balls. -/

noncomputable section
namespace KadisonSimilarity

open Filter Topology BoundedHochschild HochschildNormalPart
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

theorem gnsCyclicSpace_eq_top :
    cyclicSpace τ.gnsStarAlgHom (gnsTracialVector τ 1) = ⊤ := by
  apply top_unique
  intro ξ _
  refine (gnsTracialVector_dense τ).induction_on ξ
    (cyclicSpace_closed τ.gnsStarAlgHom (gnsTracialVector τ 1)) ?_
  intro a
  have he : gnsTracialVector τ a = τ.gnsStarAlgHom a (gnsTracialVector τ 1) := by
    rw [gnsTracialVector_left, mul_one]
  rw [he]
  exact cyclicSpace_mul τ.gnsStarAlgHom (gnsTracialVector τ 1) a
    (cyclicSpace_mem τ.gnsStarAlgHom (gnsTracialVector τ 1))

theorem gnsCyclic_coefficient_normal (hτ : TraceInPredual e τ) (η : τ.GNS) :
    coefficient τ.gnsStarAlgHom η (gnsTracialVector τ 1) ∈ normalDual e := by
  have hΩ : coefficient τ.gnsStarAlgHom (gnsTracialVector τ 1)
      (gnsTracialVector τ 1) ∈ normalDual e := by
    obtain ⟨z, hz⟩ := hτ
    apply (mem_normalDual e _).mpr
    refine ⟨z, fun a => ?_⟩
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one,
      gnsTracialVector_inner, star_one, one_mul] using hz a
  apply cyclic_coefficients_normal e τ.gnsStarAlgHom
    (gnsTracialVector τ 1) (gnsTracialVector τ 1) hΩ
  rw [gnsCyclicSpace_eq_top]
  trivial

theorem gnsVector_predual_tendsto (hτ : TraceInPredual e τ)
    {I : Type*} {l : Filter I} {a : I → A} {b : A}
    (h : PredualTendsto e a l b) (η : τ.GNS) :
    Tendsto (fun i => inner ℂ η (gnsTracialVector τ (a i))) l
      (𝓝 (inner ℂ η (gnsTracialVector τ b))) := by
  obtain ⟨z, hz⟩ := (mem_normalDual e _).mp (gnsCyclic_coefficient_normal e τ hτ η)
  have he (c : A) : inner ℂ η (gnsTracialVector τ c) = star (e.symm c z) := by
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one] using hz c
  simpa only [he] using (h z).star

theorem predual_gns_trace_balls_closed (hτ : TraceInPredual e τ) (C : ℝ) :
    IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
  apply IsSeqClosed.isClosed
  intro v ξ hv hlim
  choose a ha he using hv
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b, hb, hpre⟩ := exists_predual_ultralimit e ω a C
    (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using ha n)
  refine ⟨b, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  · apply ext_inner_left ℂ
    intro η
    have hstrong : Tendsto (fun n => inner ℂ η (v n)) (ω : Filter ℕ)
        (𝓝 (inner ℂ η ξ)) := ((tendsto_const_nhds.inner hlim).mono_left hω)
    have hweak := gnsVector_predual_tendsto e τ hτ hpre η
    have heq (n : ℕ) : inner ℂ η (gnsTracialVector τ (a n)) = inner ℂ η (v n) :=
      congrArg (inner ℂ η) (he n)
    exact tendsto_nhds_unique (hweak.congr heq) hstrong

/-- Banach-predual normality supplies exactly the GNS normality required by
the finite-factor commutator argument. -/
theorem hasNormalGNS_of_predual (hτ : TraceInPredual e τ)
    (htr : ∀ a b, τ (a * b) = τ (b * a)) : HasNormalGNS τ :=
  (gnsTracialGeometry τ htr).normal_range_of_closed_trace_balls
    (predual_gns_trace_balls_closed e τ hτ)

end KadisonSimilarity

end

end OAI
