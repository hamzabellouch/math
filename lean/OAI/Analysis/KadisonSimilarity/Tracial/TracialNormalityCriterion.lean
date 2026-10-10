import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry

namespace OAI

/-! Closed bounded trace-vector sets identify the represented bicommutant
with the original tracial algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem normal_range_of_closed_trace_balls
    (hclosed : ∀ C : ℝ, IsClosed (G.vector '' Metric.closedBall (0 : A) C)) :
    G.left.range = (representationVonNeumannAlgebra G.left).toStarSubalgebra := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra G.left a
  · intro hT
    have hv : T (G.vector 1) ∈ G.vector '' Metric.closedBall (0 : A) (‖T‖ + 1) := by
      apply (hclosed _).closure_subset
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min (ε / 2) 1
      have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
      obtain ⟨a, ha, happrox, _⟩ := twoVectorKaplanskyInput G.left T hT
        (G.vector 1) (G.vector 1) δ hδ
      refine ⟨G.vector a, ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          ha.trans (add_le_add le_rfl (min_le_right (ε / 2) 1))
      · rw [dist_eq_norm, norm_sub_rev, ← mul_one a, ← G.left_vector]
        exact happrox.trans_lt ((min_le_left (ε / 2) 1).trans_lt (by linarith))
    obtain ⟨a, _, ha⟩ := hv
    refine ⟨a, ?_⟩
    ext x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    have hTc : T ∈ Set.centralizer (Set.centralizer (Set.range G.left)) := by
      change T ∈ representationVonNeumannAlgebra G.left at hT
      rwa [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    have hc : G.right b * T = T * G.right b := hTc (G.right b) (by
      rintro _ ⟨c, rfl⟩
      exact (G.right_left c b).symm)
    have hcv := congrArg (fun R : H →L[ℂ] H => R (G.vector 1)) hc
    change G.right b (T (G.vector 1)) = T (G.right b (G.vector 1)) at hcv
    rw [G.right_vector, one_mul, ← ha, G.right_vector] at hcv
    exact (G.left_vector a b).trans hcv

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
