import OAI.Analysis.KadisonSimilarity.Tracial.TracialNormalityCriterion

namespace OAI

/-! Closed trace-vector balls persist in the bounded L²-generated algebra.
This proves normality on its own cyclic Hilbert space, not only on the
ambient representation space. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem trace_balls_closed_of_normal_range
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra) (C : ℝ) :
    IsClosed (G.vector '' Metric.closedBall (0 : A) C) := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  have hv (a : A) : (e a : H →L[ℂ] H) τ.vector = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have heq : G.vector '' Metric.closedBall (0 : A) C =
      {ξ | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ} := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨e a, ?_, hv a⟩
      rw [StarAlgEquiv.norm_map]
      simpa only [Metric.mem_closedBall, dist_zero_right] using ha
    · rintro ⟨b, hb, hξ⟩
      obtain ⟨a, rfl⟩ := e.surjective b
      refine ⟨a, ?_, (hv a).symm.trans hξ⟩
      change ‖e a‖ ≤ C at hb
      rw [StarAlgEquiv.norm_map] at hb
      simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  rw [heq]
  exact trace_ball_isClosed τ C

theorem l2Generated_trace_balls_closed
    (hclosed : ∀ C : ℝ, IsClosed (G.vector '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) (C : ℝ) :
    IsClosed ((G.baseGeometry (G.l2GeneratedAlgebra S)).vector ''
      Metric.closedBall (0 : G.l2GeneratedAlgebra S) C) := by
  let L := G.l2GeneratedAlgebra S
  have heq : (G.baseGeometry L).vector '' Metric.closedBall (0 : L) C =
      Subtype.val ⁻¹' (G.vector '' Metric.closedBall (0 : A) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : A), ha, rfl⟩
    · rintro ⟨a, ha, hξ⟩
      have hmem : a ∈ L := by
        change G.vector a ∈ G.baseSpace S.topologicalClosure
        rw [hξ, G.baseSpace_topologicalClosure]
        exact (le_of_eq (G.baseSpace_l2GeneratedAlgebra S)) ξ.property
      refine ⟨⟨a, hmem⟩, ha, ?_⟩
      exact Subtype.ext hξ
  rw [heq]
  exact (hclosed C).preimage continuous_subtype_val

theorem l2Generated_normal_baseRange
    (hclosed : ∀ C : ℝ, IsClosed (G.vector '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) :
    (G.baseGeometry (G.l2GeneratedAlgebra S)).left.range =
      (representationVonNeumannAlgebra
        (G.baseGeometry (G.l2GeneratedAlgebra S)).left).toStarSubalgebra :=
  (G.baseGeometry (G.l2GeneratedAlgebra S)).normal_range_of_closed_trace_balls
    (G.l2Generated_trace_balls_closed hclosed S)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
