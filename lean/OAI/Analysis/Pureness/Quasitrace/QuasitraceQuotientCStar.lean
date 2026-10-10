import OAI.Analysis.Pureness.Quasitrace.QuasitraceNullApproximateUnit

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

lemma cauchyQuotient_norm_square_le (x : T.CauchyQuotient hadd) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  obtain ⟨v,hv,hvn⟩ := T.cauchyQuotient_norm_lt_rep hadd
    (star (T.cauchyQuotientMap hadd u)*T.cauchyQuotientMap hadd u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ T.nullSequenceIdeal hadd := by
    change (T.nullSequenceIdeal hadd).ringCon w 0
    apply Quotient.exact
    change T.cauchyQuotientMap hadd w = T.cauchyQuotientMap hadd 0
    simp only [w,map_sub,map_mul,T.cauchyQuotientMap_star,hv,sub_self]
    exact (_root_.map_zero (T.cauchyQuotientMap hadd)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := T.exists_null_contraction hadd hw (half_pos hε)
  have heq : T.cauchyQuotientMap hadd e = 0 := Quotient.sound he
  have hmap : T.cauchyQuotientMap hadd (u*(1-e)) = T.cauchyQuotientMap hadd u := by
    simp [map_mul,map_sub,heq]
  have hun := T.cauchyQuotientMap_norm_le hadd (u*(1-e))
  rw [hmap] at hun
  have hidentity : star (u*(1-e))*(u*(1-e)) =
      (1-e)*v*(1-e)+(1-e)*(w*(1-e)) := by
    simp only [star_mul,star_sub,star_one,hestar.star_eq,w]
    noncomm_ring
  have hterm1 : ‖(1-e)*v*(1-e)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖1-e‖*‖v‖*‖1-e‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖v‖*1 := by gcongr
      _ = ‖v‖ := by ring
  have hterm2 : ‖(1-e)*(w*(1-e))‖ < ε/2 := by
    calc
      _ ≤ ‖1-e‖*‖w*(1-e)‖ := norm_mul_le _ _
      _ ≤ 1*‖w*(1-e)‖ := by gcongr
      _ < ε/2 := by simpa using hwe
  calc
    _ ≤ ‖u*(1-e)‖*‖u*(1-e)‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖star (u*(1-e))*(u*(1-e))‖ := (CStarRing.norm_star_mul_self (x := u*(1-e))).symm
    _ ≤ ‖(1-e)*v*(1-e)‖+‖(1-e)*(w*(1-e))‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (T.cauchyQuotientMap hadd u)*T.cauchyQuotientMap hadd u‖+ε := by linarith

instance cauchyQuotientCStarAlgebra : CStarAlgebra (T.CauchyQuotient hadd) where
  norm_mul_self_le := T.cauchyQuotient_norm_square_le hadd

/-- The real scalar structure inherited from the complex C⋆-algebra. -/
instance cauchyQuotientRealAlgebra : Algebra ℝ (T.CauchyQuotient hadd) :=
  Algebra.restrictScalars ℝ ℂ (T.CauchyQuotient hadd)

instance cauchyQuotientRealStarModule : StarModule ℝ (T.CauchyQuotient hadd) :=
  StarModule.complexToReal
end CuntzPureness.PositiveQuasitrace

end

end OAI
