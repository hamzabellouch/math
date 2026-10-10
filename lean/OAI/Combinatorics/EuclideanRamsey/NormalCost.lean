import OAI.Combinatorics.EuclideanRamsey.ColoringCompactness

namespace OAI

universe uGroup uAction uPoint uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators commutatorElement
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

def SameOrbit (x y : X) : Prop := ∃ h : H,h • x=y
lemma SameOrbit.refl (x : X) : SameOrbit (H:=H) x x := ⟨1,one_smul _ _⟩
lemma SameOrbit.symm {x y : X} (h : SameOrbit (H:=H) x y) : SameOrbit (H:=H) y x := by
  obtain ⟨h,rfl⟩ := h
  exact ⟨h⁻¹,inv_smul_smul h x⟩
lemma SameOrbit.trans {x y z : X} (h : SameOrbit (H:=H) x y) (h' : SameOrbit (H:=H) y z) :
    SameOrbit (H:=H) x z := by
  obtain ⟨h,rfl⟩ := h
  obtain ⟨g,rfl⟩ := h'
  exact ⟨g*h,mul_smul _ _ _⟩
lemma SameOrbit.smul (x : X) (h : H) : SameOrbit (H:=H) x (h•x) := ⟨h,rfl⟩

structure NormalCost (L : Subgroup G) where
  cost : G → ℝ
  nonneg : ∀ g,0≤cost g
  one : cost 1=0
  inv : ∀ g∈L,cost g⁻¹=cost g
  conj : ∀ g∈L,∀ k,cost (k*g*k⁻¹)=cost g
  mul : ∀ g∈L,∀ h∈L,cost (g*h)≤cost g+cost h
namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)
omit [L.Normal] in
lemma list_mem (l : List G) (h : ∀ g∈l,g∈L) : l.prod∈L := L.list_prod_mem h
omit [L.Normal] in
lemma list_bound (l : List G) (h : ∀ g∈l,g∈L) :
    c.cost l.prod ≤ (l.map c.cost).sum := by
  induction l with
  | nil => simp [c.one]
  | cons g l ih =>
    have hg := h g (by simp)
    have hl : ∀ x∈l,x∈L := fun x hx => h x (by simp [hx])
    exact (c.mul g hg l.prod (L.list_prod_mem hl)).trans (by simpa using add_le_add_left (ih hl) (c.cost g))
omit [L.Normal] in
lemma list_bound_const (l : List G) (h : ∀ g∈l,g∈L) (B : ℝ) (hB : ∀ g∈l,c.cost g≤B) :
    c.cost l.prod ≤ (l.length:ℝ)*B := by
  refine (c.list_bound l h).trans ?_
  induction l with
  | nil => simp
  | cons g l ih =>
    have hh := ih (fun x hx => h x (by simp [hx])) (fun x hx => hB x (by simp [hx]))
    simpa [Nat.cast_add,Nat.cast_one,add_mul,add_comm] using add_le_add (hB g (by simp)) hh

lemma product_difference {α : Type uAlpha} (l : List α) (a b : α → G)
    (h : ∀ j∈l,a j*(b j)⁻¹∈L) :
    (l.map a).prod*((l.map b).prod)⁻¹∈L ∧
    c.cost ((l.map a).prod*((l.map b).prod)⁻¹) ≤
      (l.map (fun j => c.cost (a j*(b j)⁻¹))).sum := by
  induction l with
  | nil => simp [c.one,L.one_mem]
  | cons j l ih =>
    obtain ⟨hm,hc⟩ := ih (fun k hk => h k (by simp [hk]))
    have hj := h j (by simp)
    let z := (l.map a).prod*((l.map b).prod)⁻¹
    have he : (a j*(l.map a).prod)*(b j*(l.map b).prod)⁻¹ =
        (a j*z*(a j)⁻¹)*(a j*(b j)⁻¹) := by dsimp [z]; group
    have hz : a j*z*(a j)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hm _
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he]
    refine ⟨L.mul_mem hz hj,?_⟩
    exact (c.mul _ hz _ hj).trans (by rw [c.conj z hm]; linarith)
end NormalCost

lemma product_difference_mem {N : Subgroup G} [N.Normal] {α : Type uAlpha}
    (l : List α) (a b : α → G) (h : ∀ j∈l,a j*(b j)⁻¹∈N) :
    (l.map a).prod*((l.map b).prod)⁻¹∈N := by
  let q := QuotientGroup.mk' N
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((l.map a).prod*((l.map b).prod)⁻¹)=1
  rw [map_mul,map_inv,mul_inv_eq_one]
  simp only [map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv] using h j hj

noncomputable def groupList (H : Type uAction) [Fintype H] : List H := (Finset.univ : Finset H).toList
omit [Group H] in
lemma groupList_mem [Fintype H] (h : H) : h∈groupList H := by
  classical
  simp [groupList]
omit [Group H] in
lemma groupList_length [Fintype H] : (groupList H).length=Fintype.card H := by
  classical
  simp [groupList]
lemma groupList_mul_perm [Fintype H] (h : H) :
    ((groupList H).map (·*h)).Perm (groupList H) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
    (Finset.nodup_toList _)).mpr
  intro g
  simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,iff_true]
  exact ⟨g*h⁻¹,by group⟩

noncomputable def orbitAverage [Fintype H] (w : X → G) (x : X) : G :=
  ((groupList H).map (fun h => w (h•x))).prod

lemma orbitAverage_preserves [Fintype H] (N : Subgroup G) [N.Normal]
    (w : X → G) (x y : X)
    (h : ∀ g : H,w (g•x)*(w (g•y))⁻¹∈N) :
    orbitAverage (H:=H) w x*(orbitAverage (H:=H) w y)⁻¹∈N :=
  product_difference_mem _ _ _ (fun g _ => h g)

lemma orbitAverage_derived [Fintype H] (N : Subgroup G) [N.Normal]
    (w : X → G) (x y : X) (horbit : SameOrbit (H:=H) x y)
    (hw : ∀ g : H,w (g•x)∈N) :
    orbitAverage (H:=H) w x*(orbitAverage (H:=H) w y)⁻¹∈⁅N,N⁆ := by
  obtain ⟨h,rfl⟩ := horbit
  let q := QuotientGroup.mk' ⁅N,N⁆
  rw [← div_eq_mul_inv]
  apply QuotientGroup.eq_iff_div_mem.mp
  change q (orbitAverage (H:=H) w x)=q (orbitAverage (H:=H) w (h•x))
  simp only [orbitAverage,map_list_prod,List.map_map]
  have hp := (groupList_mul_perm h).map (fun g => q (w (g•x)))
  simp only [List.map_map,Function.comp_def,mul_smul] at hp
  symm
  apply hp.prod_eq'
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro g k
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.commutator_mem_commutator (by simpa only [mul_smul] using hw (g*h))
      (by simpa only [mul_smul] using hw (k*h)))
end EuclideanRamsey

end

end OAI
