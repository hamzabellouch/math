import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularTotalDifferential

namespace OAI

section
namespace FilteredEdge.Data
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
variable (K : FilteredEdge.Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ) (hp : K.FC (p-2)=⊥)
def edgeCycles : K.current.Z₂ p →ₗ[R] LinearMap.ker K.current.e :=
  (K.current.Z₂ p).subtype.codRestrict _ (fun x => by
    have hx := x.property.2
    change K.e x.val∈K.FC (p-2) at hx
    rw [hp] at hx
    exact hx)
def edgeLift : K.current.Z₂ p →ₗ[R] K.current.H ⧸ K.current.filtration (p-1) :=
  (K.current.filtration (p-1)).mkQ.comp (K.current.π.comp (K.edgeCycles p hp))
omit [IsNoetherianRing R] in
lemma boundary_in_edge_kernel :
    (K.current.B₂ p).comap (K.current.Z₂ p).subtype ≤ LinearMap.ker (K.edgeLift p hp) := by
  intro x hx
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a,ha,haz⟩ := hz.1
  change y+z=x.val at hyz
  change K.d a=z at haz
  have hez : K.e z=0 := by
    rw [←haz]; exact congrArg (fun f : A →ₗ[R] C => f a) K.ed
  have hex : K.e x.val=0 := (K.edgeCycles p hp x).property
  have hey : K.e y=0 := by
    rw [←hyz,map_add,hez,add_zero] at hex
    exact hex
  change K.edgeLift p hp x=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨⟨y,hey⟩,hy.1⟩,?_⟩
  change K.current.π ⟨y,hey⟩=K.current.π (K.edgeCycles p hp x)
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-a,?_⟩
  apply Subtype.ext
  change K.d (-a)=y-x.val
  rw [map_neg,haz,←hyz]
  abel
def edgeMap : K.current.E₂ p →ₗ[R] K.current.H ⧸ K.current.filtration (p-1) :=
  ((K.current.B₂ p).comap (K.current.Z₂ p).subtype).liftQ
    (K.edgeLift p hp) (K.boundary_in_edge_kernel p hp)
omit [IsNoetherianRing R] in
lemma edge_kernel_le_tower (N : ℤ) (hN : K.FA N=⊤) :
    LinearMap.ker (K.edgeMap p hp) ≤ K.tower p N := by
  intro z hz
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    ((K.current.B₂ p).comap (K.current.Z₂ p).subtype) z
  have hx : K.edgeLift p hp x=0 := hz
  have hx' : K.current.π (K.edgeCycles p hp x)∈K.current.filtration (p-1) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y,hy⟩ := hx'
  have hxy : K.current.π (K.edgeCycles p hp x-y.val)=0 := by
    rw [map_sub,show K.current.π y.val=K.current.π (K.edgeCycles p hp x) from hy,sub_self]
  obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxy
  have hav : K.d a=x.val-y.val.val := congrArg Subtype.val ha
  have had : K.d a∈K.FB p := by
    rw [hav]
    exact (K.FB p).sub_mem x.property.1 (K.monoB (by omega) y.property)
  refine ⟨⟨a,by rw [hN]; trivial,had⟩,?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change K.d a-x.val∈K.current.B₂ p
  rw [hav,sub_sub_cancel_left]
  apply Submodule.mem_sup_left
  refine ⟨(K.FB (p-1)).neg_mem y.property,?_⟩
  change K.e (-y.val.val)∈K.FC (p-2)
  have hey : K.e y.val.val=0 := y.val.property
  rw [map_neg,hey,neg_zero]
  exact Submodule.zero_mem _
include hp in
lemma finite_edge (N : ℤ) (hN : K.FA N=⊤)
    [Module.Finite R K.current.H] [Module.Finite R (K.tower p N)] :
    Module.Finite R (K.current.E₂ p) := by
  let f := K.edgeMap p hp
  have : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_injective (Submodule.inclusion (K.edge_kernel_le_tower p hp N hN))
      (Submodule.inclusion_injective _)
  have : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_injective (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite R (K.current.E₂ p ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)
lemma finite_tower (r : ℕ)
    (hfinite : ∀i:ℕ, i<r → Module.Finite R (K.previous.E₂ (p+i+2))) :
    Module.Finite R (K.tower p (p+r+1)) := by
  induction r with
  | zero => rw [Nat.cast_zero,add_zero,K.tower_start]; infer_instance
  | succ r ih =>
    have := ih (fun i hi => hfinite i (by omega))
    have := hfinite r (by omega)
    have he : p+(r+1:ℕ)+1=p+r+2 := by push_cast; omega
    rw [he]
    have : Module.Finite R (K.tower p (p+r+2-1)) := by
      rw [show p+(r:ℤ)+2-1=p+r+1 by ring]
      exact ih (fun i hi => hfinite i (by omega))
    exact K.finite_tower_step p (p+r+2) (by omega)
end FilteredEdge.Data

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma lift_first_cycle (q : ℕ) (y : ConcreteHomology.Cycles (K.X 1) q)
    (z : (K.X 0).X (q+1)) (hz : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val) :
    ∃ x : (filteredData K (1+q)).Z₂ 2, projection K 1 q (1+q) x.val=y.val := by
  have hw : (K.total c).d (0+q+1) (0+q) (lift K 0 q y.val (-z))=0 := by
    apply (Submodule.mem_bot R).mp
    rw [←filtration_zero K (0+q)]
    apply lower_filtration K 0 q (d_lift_mem K 0 q y (-z))
    rw [d_lift_top,map_neg,hz,add_neg_cancel]
  have aux : ∃ x : (filteredData K (0+q+1)).Z₂ 2,
      projection K 1 q (0+q+1) x.val=y.val := by
    refine ⟨⟨lift K 0 q y.val (-z),lift_mem K 0 q y.val (-z),?_⟩,lift_left K 0 q y.val (-z)⟩
    change (K.total c).d (0+q+1) (0+q+1-1) (lift K 0 q y.val (-z))∈filtration K (0+q+1-1) (2-2)
    rw [Nat.add_sub_cancel,hw]
    exact Submodule.zero_mem _
  rw [show 1+q=0+q+1 by omega]
  exact aux
lemma first_lead_surjective (q : ℕ) : Function.Surjective (lead K 1 q) := by
  intro v
  obtain ⟨w,rfl⟩ := ConcreteHomology.π_surjective (row K q) 1 v
  obtain ⟨y,hy⟩ := ConcreteHomology.π_surjective (K.X 1) q w.val
  have hdy : ConcreteHomology.π (K.X 0) q
      (ConcreteHomology.cyclesMap (K.d 1 0) q y)=0 := by
    rw [←ConcreteHomology.map_π,hy]
    exact w.property
  obtain ⟨z,hz⟩ := (ConcreteHomology.π_eq_zero _ _ _).mp hdy
  have hzv : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val := by
    have h := congrArg Subtype.val hz
    change (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val at h
    exact h
  obtain ⟨x,hx⟩ := lift_first_cycle K q y z hzv
  refine ⟨x,?_⟩
  change ConcreteHomology.π (row K q) 1 (topRowCycle K 1 q x)=_
  congr 1
  apply Subtype.ext
  change ConcreteHomology.π (K.X 1) q (topCycle K 1 q x)=w.val
  rw [show topCycle K 1 q x=y by apply Subtype.ext; exact hx,hy]
end E2Leading

end

end OAI
