import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientNorm

namespace OAI
noncomputable section
namespace CuntzPureness.ClosedStarIdeal
open Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (J : ClosedStarIdeal D)

def idealStarAlgebra : NonUnitalStarSubalgebra ℂ (D) where
  carrier := J.ideal
  zero_mem' := (J.ideal).zero_mem
  add_mem' := (J.ideal).add_mem
  mul_mem' {u v} _ hv := (J.ideal).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ J.ideal
    rw [Algebra.smul_def]
    exact (J.ideal).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := J.star_mem

instance idealStarAlgebraCompleteSpace : CompleteSpace (J.idealStarAlgebra) :=
  (J.isClosed).completeSpace_coe
instance idealStarAlgebraCStar : NonUnitalCStarAlgebra (J.idealStarAlgebra) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1

instance idealPartialOrder : PartialOrder (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrder _
instance idealStarOrderedRing : StarOrderedRing (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrderedRing _

local instance : LE (J.idealStarAlgebra) := (J.idealPartialOrder).toLE
local instance : Preorder (J.idealStarAlgebra) := (J.idealPartialOrder).toPreorder

def idealInclusion : J.idealStarAlgebra →⋆ₙₐ[ℂ] D where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma idealInclusion_nonneg {e : J.idealStarAlgebra} (he : 0 ≤ e) :
    0 ≤ (e : D) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _

lemma norm_one_sub {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : D) he

lemma exists_ideal_contraction {w : D} (hw : w ∈ J.ideal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, e ∈ J.ideal ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : J.idealStarAlgebra := ⟨w,hw⟩
  let l := CStarAlgebra.approximateUnit (J.idealStarAlgebra)
  have hl := CStarAlgebra.increasingApproximateUnit (J.idealStarAlgebra)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,norm_one_sub (J.idealInclusion_nonneg hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm

lemma quotient_norm_square_le (x : J.Quotient) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep
    (star (J.quotientMap u)*J.quotientMap u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.ideal := by
    change (J.ideal).ringCon w 0
    apply Quotient.exact
    change J.quotientMap w = J.quotientMap 0
    simp only [w,map_sub,map_mul,J.quotientMap_star,hv,sub_self]
    exact (_root_.map_zero (J.quotientMap)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := J.exists_ideal_contraction hw (half_pos hε)
  have heq : J.quotientMap e = 0 := Quotient.sound he
  have hmap : J.quotientMap (u*(1-e)) = J.quotientMap u := by
    simp [map_mul,map_sub,heq]
  have hun := J.quotientMap_norm_le (u*(1-e))
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
    _ ≤ ‖star (J.quotientMap u)*J.quotientMap u‖+ε := by linarith

instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := J.quotient_norm_square_le
end CuntzPureness.ClosedStarIdeal

end

end OAI
