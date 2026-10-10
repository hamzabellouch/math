import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

section Finite
variable {I D : Type*} [DecidableEq I] [DecidableEq D]
noncomputable def offFiberPairs (f : I → D) (X : Finset I) : Finset (I × I) :=
  (X ×ˢ X).filter fun p => f p.1 ≠ f p.2

omit [DecidableEq I] in
lemma card_offFiberPairs (f : I → D) (X : Finset I) :
    (offFiberPairs f X).card = ∑ y ∈ X, (X.filter fun z => f y ≠ f z).card := by
  simp only [offFiberPairs,Finset.card_filter,Finset.sum_product]

omit [DecidableEq I] in
lemma offFiberPairs_many (f : I → D) (X : Finset I)
    (h : ∀ y ∈ X, 2*(X.filter fun z => f y = f z).card ≤ X.card) :
    X.card^2 ≤ 2*(offFiberPairs f X).card := by
  have hrow (y : I) (hy : y ∈ X) : X.card ≤ 2*(X.filter fun z => f y ≠ f z).card := by
    have hp := Finset.card_filter_add_card_filter_not (s := X) (fun z => f y = f z)
    change (X.filter fun z => f y = f z).card + (X.filter fun z => f y ≠ f z).card = X.card at hp
    have hh := h y hy
    omega
  have hs := Finset.sum_le_sum hrow
  simpa only [Finset.sum_const_nat,← Finset.mul_sum,← card_offFiberPairs,pow_two] using hs
end Finite

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V)

noncomputable def onPlane (X : Finset {y : ℙ K V // x ≠ y}) (A : Submodule K V) :=
  X.filter fun y => y.val.submodule ≤ A

noncomputable def planePairs (X : Finset {y : ℙ K V // x ≠ y}) (A : Submodule K V) :=
  offFiberPairs (fun y : {y : ℙ K V // x ≠ y} => RadialLine.through x y.val y.property) (onPlane x X A)

lemma planePairs_disjoint (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B) (hne : A ≠ B) :
    Disjoint (planePairs x X A) (planePairs x X B) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨y,z⟩ hpa hpb
  obtain ⟨hya,hza⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpa).1
  obtain ⟨hyb,hzb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpb).1
  have hrad := (Finset.mem_filter.mp hpa).2
  let l := RadialLine.through x y.val y.property
  let m := RadialLine.through x z.val z.property
  have hr : finrank K (l.val ⊔ m.val : Submodule K V) = 3 := RadialLine.finrank_sup hrad
  have hlA : l.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hya).2⟩
  have hmA : m.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hza).2⟩
  have hlB : l.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hyb).2⟩
  have hmB : m.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hzb).2⟩
  have hEA := Submodule.eq_of_le_of_finrank_eq (sup_le hlA hmA) (hr.trans hA.symm)
  have hEB := Submodule.eq_of_le_of_finrank_eq (sup_le hlB hmB) (hr.trans hB.symm)
  exact hne (hEA.symm.trans hEB)

theorem rich_nondominant_plane_count (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (onPlane x X A).card)
    (hnd : ∀ A ∈ F, ∀ l : RadialLine x,
      2*((onPlane x X A).filter fun y => y.val.submodule ≤ l.val).card ≤ (onPlane x X A).card) :
    F.card*M^2 ≤ 2*X.card^2 := by
  have hm (A : Submodule K V) (hA : A ∈ F) : M^2 ≤ 2*(planePairs x X A).card := by
    have hh := offFiberPairs_many (fun y : {y : ℙ K V // x ≠ y} => RadialLine.through x y.val y.property)
      (onPlane x X A) (by
        intro y _
        have hr := hnd A hA (RadialLine.through x y.val y.property)
        have he : ((onPlane x X A).filter fun z =>
            RadialLine.through x y.val y.property = RadialLine.through x z.val z.property) =
            ((onPlane x X A).filter fun z => z.val.submodule ≤ (RadialLine.through x y.val y.property).val) := by
          ext z
          simp only [Finset.mem_filter,eq_comm (a := RadialLine.through x y.val y.property),RadialLine.through_eq_iff]
        rwa [he])
    exact (Nat.pow_le_pow_left (hM A hA) 2).trans hh
  have hdisj : (F : Set (Submodule K V)).PairwiseDisjoint (planePairs x X) := by
    intro A hA B hB hne
    exact planePairs_disjoint x X A B (hF A hA) (hF B hB) (hxF A hA) (hxF B hB) hne
  have hsub : F.biUnion (planePairs x X) ⊆ X ×ˢ X := by
    intro p hp
    obtain ⟨A,_,hpA⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hy,hz⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpA).1
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hz).1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj,Finset.card_product] at hc
  have hs := Finset.sum_le_sum hm
  simp only [Finset.sum_const_nat,← Finset.mul_sum] at hs
  exact hs.trans (by nlinarith)

end SharpRamseyFive.NondominantOverlap

end OAI
