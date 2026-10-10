import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRealImag
import Mathlib.Analysis.Normed.Group.Quotient

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

abbrev nullSequenceSubmodule : Submodule ℂ (T.cauchySequenceAlgebra hadd) :=
  (T.cauchyQuotientMap hadd).toLinearMap.ker

lemma nullSequenceSubmodule_coe :
    (T.nullSequenceSubmodule hadd : Set (T.cauchySequenceAlgebra hadd)) =
      (T.nullSequenceIdeal hadd : Set (T.cauchySequenceAlgebra hadd)) := by
  ext u
  change T.cauchyQuotientMap hadd u = 0 ↔ u ∈ T.nullSequenceIdeal hadd
  change (T.nullSequenceIdeal hadd).ringCon.mk' u = (T.nullSequenceIdeal hadd).ringCon.mk' 0 ↔ _
  exact Quotient.eq

instance nullSequenceSubmodule_closed : IsClosed (T.nullSequenceSubmodule hadd : Set (T.cauchySequenceAlgebra hadd)) := by
  rw [T.nullSequenceSubmodule_coe hadd]
  exact T.nullSequenceIdeal_isClosed hadd

def cauchyQuotientLinearEquiv :
    (T.cauchySequenceAlgebra hadd ⧸ T.nullSequenceSubmodule hadd) ≃ₗ[ℂ] T.CauchyQuotient hadd :=
  (T.cauchyQuotientMap hadd).toLinearMap.quotKerEquivOfSurjective (T.cauchyQuotientMap_surjective hadd)

lemma cauchyQuotientLinearEquiv_mk (u : T.cauchySequenceAlgebra hadd) :
    T.cauchyQuotientLinearEquiv hadd (Submodule.Quotient.mk u) = T.cauchyQuotientMap hadd u := rfl

instance cauchyQuotientNormedAddCommGroup : NormedAddCommGroup (T.CauchyQuotient hadd) :=
  NormedAddCommGroup.induced _ _ (T.cauchyQuotientLinearEquiv hadd).symm
    (T.cauchyQuotientLinearEquiv hadd).symm.injective

instance cauchyQuotientNormedSpace : NormedSpace ℂ (T.CauchyQuotient hadd) :=
  NormedSpace.induced ℂ _ _ (T.cauchyQuotientLinearEquiv hadd).symm

def cauchyQuotientNormEquiv : T.CauchyQuotient hadd ≃ₗᵢ[ℂ]
    (T.cauchySequenceAlgebra hadd ⧸ T.nullSequenceSubmodule hadd) where
  __ := (T.cauchyQuotientLinearEquiv hadd).symm
  norm_map' _ := rfl

lemma cauchyQuotientMap_norm_le (u : T.cauchySequenceAlgebra hadd) :
    ‖T.cauchyQuotientMap hadd u‖ ≤ ‖u‖ := by
  change ‖(T.cauchyQuotientLinearEquiv hadd).symm (T.cauchyQuotientMap hadd u)‖ ≤ ‖u‖
  rw [← T.cauchyQuotientLinearEquiv_mk hadd, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u

lemma cauchyQuotient_norm_lt_rep (x : T.CauchyQuotient hadd) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : T.cauchySequenceAlgebra hadd, T.cauchyQuotientMap hadd u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((T.cauchyQuotientLinearEquiv hadd).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (T.cauchyQuotientLinearEquiv hadd).symm.injective
  rw [← T.cauchyQuotientLinearEquiv_mk hadd,LinearEquiv.symm_apply_apply,hu]

instance cauchyQuotientCompleteSpace : CompleteSpace (T.CauchyQuotient hadd) :=
  (T.cauchyQuotientNormEquiv hadd).toIsometryEquiv.completeSpace_iff.mpr inferInstance

lemma cauchyQuotient_norm_mul_le (x y : T.CauchyQuotient hadd) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := T.cauchyQuotient_norm_lt_rep hadd x hδ
  obtain ⟨v,rfl,hv⟩ := T.cauchyQuotient_norm_lt_rep hadd y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [T.cauchyQuotientMap_norm_le hadd u]⟩
    ⟨by linarith,by linarith [T.cauchyQuotientMap_norm_le hadd v]⟩
  calc
    _ = ‖T.cauchyQuotientMap hadd (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := T.cauchyQuotientMap_norm_le hadd _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]

instance cauchyQuotientNormedRing : NormedRing (T.CauchyQuotient hadd) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := T.cauchyQuotient_norm_mul_le hadd

instance cauchyQuotientNormedAlgebra : NormedAlgebra ℂ (T.CauchyQuotient hadd) where
  norm_smul_le := norm_smul_le

lemma cauchyQuotient_norm_star (x : T.CauchyQuotient hadd) : ‖star x‖ = ‖x‖ := by
  have hle (y : T.CauchyQuotient hadd) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := T.cauchyQuotient_norm_lt_rep hadd y hε
    rw [← T.cauchyQuotientMap_star hadd]
    exact (T.cauchyQuotientMap_norm_le hadd (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

instance cauchyQuotientNormedStarGroup : NormedStarGroup (T.CauchyQuotient hadd) where
  norm_star_le x := (T.cauchyQuotient_norm_star hadd x).le

lemma cauchyQuotientStarHom_continuous : Continuous (T.cauchyQuotientStarHom hadd) := by
  exact (T.cauchyQuotientMap hadd).toLinearMap.mkContinuous 1
    (fun u => by simpa using T.cauchyQuotientMap_norm_le hadd u) |>.continuous
end CuntzPureness.PositiveQuasitrace

end

end OAI
