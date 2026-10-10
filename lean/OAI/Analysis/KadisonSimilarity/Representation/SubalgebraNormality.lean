import OAI.Analysis.KadisonSimilarity.Tracial.TracialNormalityCriterion

namespace OAI

/-! Normality of a represented subalgebra follows from closed bounded
trace-vector sets, using the original ambient tracial geometry for totality. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (S : StarSubalgebra ℂ P) [IsClosed (S : Set P)]

theorem subalgebra_normal_range_of_closed_trace_balls
    (hclosed : ∀ C : ℝ, IsClosed ((G.vector.comp S.subtype.toLinearMap) ''
      Metric.closedBall (0 : S) C)) :
    S.map G.left = (representationVonNeumannAlgebra (G.left.comp S.subtype)).toStarSubalgebra := by
  let σ := G.left.comp S.subtype
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact mem_representationVonNeumannAlgebra σ ⟨a, ha⟩
  · intro hT
    have hv : T (G.vector 1) ∈ (G.vector.comp S.subtype.toLinearMap) ''
        Metric.closedBall (0 : S) (‖T‖ + 1) := by
      apply (hclosed _).closure_subset
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min (ε / 2) 1
      have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
      obtain ⟨a, ha, happrox, _⟩ := twoVectorKaplanskyInput σ T hT
        (G.vector 1) (G.vector 1) δ hδ
      refine ⟨G.vector (a : P), ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          ha.trans (add_le_add le_rfl (min_le_right (ε / 2) 1))
      · rw [dist_eq_norm]
        change ‖T (G.vector 1) - G.vector (a : P)‖ < ε
        have hv : σ a (G.vector 1) = G.vector (a : P) := by
          change G.left (a : P) (G.vector 1) = _
          rw [G.left_vector, mul_one]
        rw [← hv, norm_sub_rev]
        exact happrox.trans_lt ((min_le_left (ε / 2) 1).trans_lt (by linarith))
    obtain ⟨a, _, ha⟩ := hv
    refine ⟨(a : P), a.property, ?_⟩
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    have hTc : T ∈ Set.centralizer (Set.centralizer (Set.range σ)) := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rwa [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    have hc : G.right b * T = T * G.right b := hTc (G.right b) (by
      rintro _ ⟨c, rfl⟩
      exact (G.right_left (c : P) b).symm)
    have hcv := congrArg (fun R : H →L[ℂ] H => R (G.vector 1)) hc
    change G.right b (T (G.vector 1)) = T (G.right b (G.vector 1)) at hcv
    change G.vector (a : P) = T (G.vector 1) at ha
    rw [G.right_vector, one_mul, ← ha, G.right_vector] at hcv
    exact (G.left_vector (a : P) b).trans hcv

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
