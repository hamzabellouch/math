import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.SolvableGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma HasPolynomialDegree.of_surjective {d : ℕ} (hg : HasPolynomialDegree A d)
    (f : A →* B) (hf : Surjective f) : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,C,hC⟩ := (hasPolynomialDegree_iff d).mp hg
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image f,Finset.mem_image.mpr ⟨1,h1,map_one f⟩,?_,?_,C,?_⟩
  · rw [←Finset.image_inv,hs]
  · rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · intro R
    obtain ⟨n,hn,hb⟩ := hC R
    refine ⟨n,hn,le_trans ?_ hb⟩
    rw [←Finset.image_pow]
    exact Finset.card_image_le

omit [DecidableEq A] [DecidableEq B] in

def powerSubgroup (A : Type*) [Group A] (k : ℕ) : Subgroup A :=
  Subgroup.closure (Set.range (fun x : A => x^k))

omit [DecidableEq A] [DecidableEq B] in
instance powerSubgroup_characteristic (k : ℕ) : (powerSubgroup A k).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro f
  rw [powerSubgroup,MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  exact ⟨f x,map_pow f x k |>.symm⟩

omit [DecidableEq A] [DecidableEq B] in
lemma powerSubgroup_le_finiteIndex (L : Subgroup A) [L.Normal] [L.FiniteIndex] :
    powerSubgroup A (Nat.card (A ⧸ L)) ≤ L := by
  apply (Subgroup.closure_le L).mpr
  rintro _ ⟨x,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' L) (x^_)=1
  rw [map_pow]
  let _ := Fintype.ofFinite (A ⧸ L)
  simpa only [Nat.card_eq_fintype_card] using
    (pow_card_eq_one (x := (QuotientGroup.mk' L) x))

omit [DecidableEq B] in
lemma powerSubgroup_finiteIndex_of_solvable_growth {d : ℕ} (hg : HasPolynomialDegree A d)
    [Group.IsSolvable A] (k : ℕ) (hk : 0 < k) : (powerSubgroup A k).FiniteIndex := by
  let P := powerSubgroup A k
  have ht : IsMulTorsion (A ⧸ P) := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective P q
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨k,hk,?_⟩
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨x,rfl⟩
  have hq := hg.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  let _ : Finite (A ⧸ P) := finite_of_torsion_solvable_sparse_growth hq ht
  exact Subgroup.finiteIndex_of_finite_quotient

omit [DecidableEq B] in

theorem HasPolynomialDegree.characteristic_nilpotent_core {d : ℕ}
    (hg : HasPolynomialDegree A d) [Group.IsSolvable A]
    (hv : Group.IsVirtuallyNilpotent A) :
    ∃ P : Subgroup A, P.Characteristic ∧ P.FiniteIndex ∧ Group.IsNilpotent P := by
  obtain ⟨L,hL,hLi⟩ := hv
  let _ := hL
  let _ := hLi
  let N := L.normalCore
  let k := Nat.card (A ⧸ N)
  have hk : 0 < k := Nat.card_pos
  let P := powerSubgroup A k
  have hPN : P≤N := powerSubgroup_le_finiteIndex N
  have hPL : P≤L := hPN.trans L.normalCore_le
  refine ⟨P,inferInstance,powerSubgroup_finiteIndex_of_solvable_growth hg k hk,?_⟩
  let f : P →* L := Subgroup.inclusion hPL
  apply Subgroup.isNilpotent_of_ker_le_center f
  rw [(MonoidHom.ker_eq_bot_iff f).mpr (Subgroup.inclusion_injective hPL)]
  exact bot_le

omit [DecidableEq A] [DecidableEq B] in
lemma characteristic_map_normal (N : Subgroup A) [N.Normal]
    (P : Subgroup N) [P.Characteristic] : (P.map N.subtype).Normal := by
  constructor
  rintro _ ⟨x,hx,rfl⟩ a
  refine ⟨(MulAut.conjNormal a) x,?_,rfl⟩
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance (MulAut.conjNormal a) hx

end CriticalPercolation.SparseGrowth
end
end

end OAI
