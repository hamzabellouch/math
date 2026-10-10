import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.FGExtensions
import OAI.Probability.CriticalPercolation.LinearGroups.SolvableGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth

lemma subgroup_fg_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → derivedSeries A n=⊥ →
      ∀ J : Subgroup A, Group.FG J := by
  induction n with
  | zero =>
    intro A _ _ d hg hz J
    have hsub : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by
        have hm : x∈derivedSeries A 0 := Subgroup.mem_top x
        simpa only [hz,Subgroup.mem_bot] using hm
      have hy : y=1 := by
        have hm : y∈derivedSeries A 0 := Subgroup.mem_top y
        simpa only [hz,Subgroup.mem_bot] using hm
      exact hx.trans hy.symm
    infer_instance
  | succ n ih =>
    intro A _ _ d hg hz J
    let _ := hg.fg
    let C := commutator A
    let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr hg.commutator_fg
    have hC : HasPolynomialDegree C d := hg.of_injective C.subtype Subtype.val_injective
    have hzC : derivedSeries C n=⊥ := by
      apply Subgroup.map_injective (f := C.subtype) Subtype.val_injective
      rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
    let K := J.subgroupOf C
    let _ : Group.FG K := ih C d hC hzC K
    let Q := A ⧸ C
    let _ : IsMulCommutative Q :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    let f := (QuotientGroup.mk' C).comp J.subtype
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    let e : K ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val.val,x.property⟩,
        (QuotientGroup.eq_one_iff _).mpr x.val.property⟩
      invFun := fun y => ⟨⟨y.val.val,(QuotientGroup.eq_one_iff _).mp y.property⟩,
        y.val.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective

variable {A : Type*} [Group A] [DecidableEq A]

theorem HasPolynomialDegree.solvable_subgroup_fg {d : ℕ} (hg : HasPolynomialDegree A d)
    [Group.IsSolvable A] (J : Subgroup A) : Group.FG J := by
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact subgroup_fg_of_derivedSeries_eq_bot n A d hg hn J

end CriticalPercolation.SparseGrowth
end
end

end OAI
