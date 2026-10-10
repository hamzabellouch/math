import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Congruence.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter
open scoped Topology NNReal ENNReal

structure ClosedStarIdeal (D : Type*) [CStarAlgebra D] where
  ideal : TwoSidedIdeal D
  star_mem : ∀ {u : D}, u ∈ ideal → star u ∈ ideal
  isClosed : IsClosed (ideal : Set D)

namespace ClosedStarIdeal
variable {D : Type*} [CStarAlgebra D] (J : ClosedStarIdeal D)

abbrev Quotient := J.ideal.ringCon.Quotient

def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ

lemma quotientMap_surjective : Function.Surjective J.quotientMap :=
  J.ideal.ringCon.mkₐ_surjective (α := ℂ)

lemma rel_star (u v : D) (h : J.ideal.ringCon u v) :
    J.ideal.ringCon (star u) (star v) := by
  rw [TwoSidedIdeal.rel_iff] at h ⊢
  simpa only [star_sub] using J.star_mem h

instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (J.rel_star)

lemma quotientMap_star (u : D) :
    J.quotientMap (star u) = star (J.quotientMap u) := rfl

instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← J.quotientMap_star,← J.quotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_mul,← J.quotientMap_star,star_mul,map_mul,
      J.quotientMap_star,J.quotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add,← J.quotientMap_star,star_add,map_add,
      J.quotientMap_star,J.quotientMap_star]

instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← _root_.map_smul,← J.quotientMap_star,star_smul,_root_.map_smul,J.quotientMap_star]

def quotientStarHom : D →⋆ₐ[ℂ] J.Quotient :=
  { J.quotientMap with map_star' := J.quotientMap_star }

abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker

lemma idealSubmodule_coe :
    (J.idealSubmodule : Set (D)) =
      (J.ideal : Set (D)) := by
  ext u
  change J.quotientMap u = 0 ↔ u ∈ J.ideal
  change (J.ideal).ringCon.mk' u = (J.ideal).ringCon.mk' 0 ↔ _
  exact Quotient.eq

instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set (D)) := by
  rw [J.idealSubmodule_coe]
  exact J.isClosed

def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective (J.quotientMap_surjective)

lemma quotientLinearEquiv_mk (u : D) :
    J.quotientLinearEquiv (Submodule.Quotient.mk u) = J.quotientMap u := rfl

instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective

instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm

def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl

lemma quotientMap_norm_le (u : D) :
    ‖J.quotientMap u‖ ≤ ‖u‖ := by
  change ‖(J.quotientLinearEquiv).symm (J.quotientMap u)‖ ≤ ‖u‖
  rw [← J.quotientLinearEquiv_mk, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u

lemma quotient_norm_lt_rep (x : J.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : D, J.quotientMap u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((J.quotientLinearEquiv).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (J.quotientLinearEquiv).symm.injective
  rw [← J.quotientLinearEquiv_mk,LinearEquiv.symm_apply_apply,hu]

instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance

lemma quotient_norm_mul_le (x y : J.Quotient) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep x hδ
  obtain ⟨v,rfl,hv⟩ := J.quotient_norm_lt_rep y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [J.quotientMap_norm_le u]⟩
    ⟨by linarith,by linarith [J.quotientMap_norm_le v]⟩
  calc
    _ = ‖J.quotientMap (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := J.quotientMap_norm_le _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]

instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := J.quotient_norm_mul_le

instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le

lemma quotient_norm_star (x : J.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : J.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep y hε
    rw [← J.quotientMap_star]
    exact (J.quotientMap_norm_le (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (J.quotient_norm_star x).le

lemma quotientStarHom_continuous : Continuous (J.quotientStarHom) := by
  exact (J.quotientMap).toLinearMap.mkContinuous 1
    (fun u => by simpa using J.quotientMap_norm_le u) |>.continuous
end ClosedStarIdeal
end CuntzPureness

end

end OAI
