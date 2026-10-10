import OAI.Analysis.AncientFlat.Evolution.TimeOneTails
import OAI.Analysis.AncientFlat.Evolution.C0Ascoli

namespace OAI
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff ZeroAtInfty
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem compact_time_one_difference (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf)
    (P Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ))
    (hP : TimeOneMap Af Bf P)
    (hPc : TimeOneMap (fun _ => c^2) (fun _ => 0) Pc) :
    IsCompactOperator (P-Pc) := by
  obtain ⟨K,hK,hKb⟩ := hP.uniform_lipschitz h
  obtain ⟨Kc,hKc,hKcb⟩ := hPc.uniform_lipschitz (SymbolBounds.constant h.1)
  let Q := P-Pc
  have hh : ∀ d : C₀(V,ℂ), d∈closedBall 0 1 → ‖d‖≤1 := by
    intro d hd
    simpa only [mem_closedBall,dist_zero_right] using hd
  have ht : TotallyBounded (Q '' closedBall 0 1) := by
    apply FlatCompactness.totallyBounded_of_lipschitz_tails _ ‖Q‖ (K+Kc) (norm_nonneg Q) (add_nonneg hK hKc)
    · rintro f ⟨d,hd,rfl⟩ x
      exact (C0Convolution.apply_norm_le (Q d) x).trans (((Q.le_opNorm d).trans
        (mul_le_mul_of_nonneg_left (hh d hd) (norm_nonneg Q))).trans_eq (mul_one _))
    · rintro f ⟨d,hd,rfl⟩ x y
      have he : Q d x-Q d y=(P d x-P d y)-(Pc d x-Pc d y) := by
        simp only [Q,sub_apply,ZeroAtInftyContinuousMap.sub_apply]
        ring
      rw [he]
      calc
        _ ≤ ‖P d x-P d y‖+‖Pc d x-Pc d y‖ := norm_sub_le _ _
        _ ≤ K*‖d‖*‖x-y‖+Kc*‖d‖*‖x-y‖ := add_le_add (hKb d x y) (hKcb d x y)
        _ = (K+Kc)*‖d‖*‖x-y‖ := by ring
        _ ≤ (K+Kc)*1*‖x-y‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hh d hd) (add_nonneg hK hKc)) (norm_nonneg _)
        _ = _ := by rw [mul_one]
    · intro ε hε
      obtain ⟨R,hR,hRb⟩ := hP.uniform_tails_difference h hPc ε hε
      refine ⟨R,hR,?_⟩
      rintro f ⟨d,hd,rfl⟩ x hx
      exact hRb d (hh d hd) x hx
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall Q.toLinearMap zero_lt_one).mpr
  exact ht.closure.isCompact_of_isClosed isClosed_closure
end FlatSimilarity

end

end OAI
