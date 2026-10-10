import OAI.Analysis.DiamondDistortion.Vanishing

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace InfimalCost
variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Quotient construction of the exact infimum over all linear representations.
    No infimum or supremum is assumed to be attained. -/
structure Presentation (E F : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] where
  output : E →ₗ[ℝ] F
  sectionMap : F →ₗ[ℝ] E
  right_inverse : ∀ v,output (sectionMap v)=v
namespace Presentation
variable (A : Presentation E F)
def seminorm : Seminorm ℝ F :=
  (normSeminorm ℝ (E ⧸ LinearMap.ker A.output)).comp ((LinearMap.ker A.output).mkQ.comp A.sectionMap)
lemma representation_eq {d : E} {v : F} (hd : A.output d=v) :
    (LinearMap.ker A.output).mkQ d=(LinearMap.ker A.output).mkQ (A.sectionMap v) := by
  change (Submodule.Quotient.mk d : E ⧸ LinearMap.ker A.output)=Submodule.Quotient.mk (A.sectionMap v)
  rw [Submodule.Quotient.eq]
  change A.output (d-A.sectionMap v)=0
  rw [map_sub,hd,A.right_inverse,sub_self]
lemma le_representation {d : E} {v : F} (hd : A.output d=v) : A.seminorm v ≤ ‖d‖ := by
  change ‖(LinearMap.ker A.output).mkQ (A.sectionMap v)‖ ≤ ‖d‖
  rw [← A.representation_eq hd]
  exact Submodule.Quotient.norm_mk_le _ d
lemma near_representation (v : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : E,A.output d=v ∧ ‖d‖ < A.seminorm v+ε := by
  obtain ⟨d,hd,hb⟩ := Submodule.Quotient.norm_mk_lt
    ((LinearMap.ker A.output).mkQ (A.sectionMap v)) hε
  refine ⟨d,?_,hb⟩
  have hh : d-A.sectionMap v ∈ LinearMap.ker A.output := (Submodule.Quotient.eq _).mp hd
  change A.output (d-A.sectionMap v)=0 at hh
  rw [map_sub,A.right_inverse,sub_eq_zero] at hh
  exact hh
lemma eq_sInf (v : F) : A.seminorm v=sInf {r : ℝ | ∃ d : E,A.output d=v ∧ ‖d‖=r} := by
  let costs := {r : ℝ | ∃ d : E,A.output d=v ∧ ‖d‖=r}
  have hn : costs.Nonempty := ⟨‖A.sectionMap v‖,A.sectionMap v,A.right_inverse v,rfl⟩
  have hb : BddBelow costs := ⟨0,by rintro r ⟨d,hd,rfl⟩; exact norm_nonneg d⟩
  apply le_antisymm
  · exact le_csInf hn (by rintro r ⟨d,hd,rfl⟩; exact A.le_representation hd)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨d,hd,hh⟩ := A.near_representation v hε
    exact (csInf_le hb ⟨d,hd,rfl⟩).trans hh.le
lemma bound (v : F) {C b : ℝ} (hC : 0 ≤ C) (hb : ∀ d : E,A.output d=v → b ≤ C*‖d‖) :
    b ≤ C*A.seminorm v := by
  by_cases hC0 : C=0
  · simpa only [hC0,zero_mul] using hb (A.sectionMap v) (A.right_inverse v)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hd,hh⟩ := A.near_representation v (div_pos hε hCpos)
  have he := (hb d hd).trans (mul_le_mul_of_nonneg_left hh.le hC)
  calc
    _ ≤ C*(A.seminorm v+ε/C) := he
    _ = C*A.seminorm v+ε := by field_simp
end Presentation
end InfimalCost

end DiamondDistortion

end

end OAI
