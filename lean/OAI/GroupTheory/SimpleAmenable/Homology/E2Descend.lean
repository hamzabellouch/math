import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FilteredEdgeReturn

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma boundary_top_cycle (p q : ℕ) (w : (K.total c).X (p+q+1))
    (hw : w∈filtration K (p+q+1) (p+2))
    (hdw : (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (p+1)) :
    (K.X (p+1)).d q (q-1) (projection K (p+1) q (p+q+1) w)=0 := by
  cases q with
  | zero => rw [(K.X (p+1)).shape 0 (0-1) (by decide)]; rfl
  | succ q =>
    rw [Nat.add_sub_cancel]
    have hd := d_entry' K (p+1) q (p+(q+1)+1) (p+(q+1)) (by omega) (by omega) w
    have hz : projection K (p+1) q (p+(q+1)) ((K.total c).d (p+(q+1)+1) (p+(q+1)) w)=0 :=
      entry_zero K hdw (by omega)
    have hf : projection K (p+1+1) q (p+(q+1)+1) w=0 := entry_zero K hw (by omega)
    rw [hz,hf,map_zero,zero_add] at hd
    have hh := congrArg (fun z => (((-1 : ℤˣ)^(p+1))⁻¹) • z) hd.symm
    rw [inv_smul_smul,smul_zero] at hh
    exact hh
lemma boundary_lead_zero (p q : ℕ) (w : (K.total c).X (p+q+1))
    (hw : w∈filtration K (p+q+1) (p+2))
    (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : x.val=(K.total c).d (p+q+1) (p+q) w) : lead K p q x=0 := by
  have hdw : (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (p+1) := hx ▸ x.property.1
  let y : ConcreteHomology.Cycles (K.X (p+1)) q :=
    ⟨projection K (p+1) q (p+q+1) w,boundary_top_cycle K p q w hw hdw⟩
  apply (ConcreteHomology.π_eq_zero (row K q) p (topRowCycle K p q x)).mpr
  refine ⟨ConcreteHomology.π (K.X (p+1)) q y,?_⟩
  apply Subtype.ext
  change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
    (ConcreteHomology.π (K.X (p+1)) q y) = ConcreteHomology.π (K.X p) q (topCycle K p q x)
  rw [ConcreteHomology.map_π]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨- (((-1 : ℤˣ)^p) • projection K p (q+1) (p+q+1) w),?_⟩
  apply Subtype.ext
  change (K.X p).d (q+1) q (- (((-1 : ℤˣ)^p) • projection K p (q+1) (p+q+1) w))=
    (ConcreteHomology.cyclesMap (K.d (p+1) p) q y).val - (topCycle K p q x).val
  rw [ConcreteHomology.cyclesMap_val]
  change _ = (K.d (p+1) p).f q (projection K (p+1) q (p+q+1) w) - projection K p q (p+q) x.val
  rw [hx,d_entry,map_neg,linear_units_smul]
  abel
lemma boundary_lead (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : x.val∈(filteredData K (p+q)).B₂ ((p:ℤ)+1)) : lead K p q x=0 := by
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx
  have hz' := (filteredData K (p+q)).B₂_le_Z₂ ((p:ℤ)+1)
    (show z∈(filteredData K (p+q)).B₂ ((p:ℤ)+1) from Submodule.mem_sup_right hz)
  let z' : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) := ⟨z,hz'⟩
  let y' : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) := x-z'
  have hy' : y'.val=y := by change x.val-z=y; rw [←hyz]; abel
  have hly : lead K p q y'=0 := by
    have ht : projection K p q (p+q) y'.val=0 := by
      rw [hy']
      exact entry_zero K hy.1 (by omega)
    have hc : topCycle K p q y'=0 := by apply Subtype.ext; exact ht
    change ConcreteHomology.π (row K q) p (topRowCycle K p q y')=0
    have hr : topRowCycle K p q y'=0 := by
      apply Subtype.ext
      change ConcreteHomology.π (K.X p) q (topCycle K p q y')=0
      rw [hc,map_zero]
    rw [hr,map_zero]
  have hlz : lead K p q z'=0 := by
    obtain ⟨w,hw,hwe⟩ := hz.1
    apply boundary_lead_zero K p q w _ z' hwe.symm
    change w∈filtration K (p+q+1) (((p:ℤ)+1)+1) at hw
    simpa only [Int.add_assoc,Int.reduceAdd] using hw
  rw [show x=y'+z' by dsimp [y']; abel,map_add,hly,hlz,add_zero]
noncomputable def descendedLead (p q : ℕ) :
    (filteredData K (p+q)).E₂ ((p:ℤ)+1) →ₗ[R] ConcreteHomology.H (row K q) p :=
  (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
    ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).liftQ (lead K p q)
      (fun x hx => boundary_lead K p q x hx)
lemma descendedLead_injective (p q : ℕ) : Function.Injective (descendedLead K p q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (lead_zero_boundary K p q y hx)
lemma first_descendedLead_surjective (q : ℕ) : Function.Surjective (descendedLead K 1 q) := by
  intro y
  obtain ⟨x,hx⟩ := first_lead_surjective K q y
  exact ⟨Submodule.Quotient.mk x,hx⟩
end E2Leading

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
noncomputable def edgeData (n : ℕ) : FilteredEdge.Data
    (R:=R) (D:=(K.total c).X (n+2)) (A:=(K.total c).X (n+1))
    (B:=(K.total c).X n) (C:=(K.total c).X (n-1)) where
  s := ((K.total c).d (n+2) (n+1)).hom
  d := ((K.total c).d (n+1) n).hom
  e := ((K.total c).d n (n-1)).hom
  ds := ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+2) (n+1) n)
  ed := ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+1) n (n-1))
  FD := filtration K (n+2)
  FA := filtration K (n+1)
  FB := filtration K n
  FC := filtration K (n-1)
  monoA := filtration_mono K (n+1)
  monoB := filtration_mono K n
lemma edgeData_current (n : ℕ) : (edgeData K n).current=filteredData K n := rfl
lemma edgeData_previous (n : ℕ) : (edgeData K n).previous=filteredData K (n+1) := rfl
end TotalProjection
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ)
    [Module.Finite R (ConcreteHomology.H (K.total c) (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R (ConcreteHomology.H (row K r) p)) :
    Module.Finite R (ConcreteHomology.H (row K q) 1) := by
  let E := edgeData K (1+q)
  have : Module.Finite R E.current.H := ‹Module.Finite R (ConcreteHomology.H (K.total c) (1+q))›
  have : Module.Finite R (E.tower 2 (2+(q:ℤ)+1)) := by
    apply E.finite_tower 2 q
    intro i hi
    have hpq : (i+3)+(q-1-i)=1+q+1 := by omega
    have := hf (i+3) (q-1-i) (by omega) (by omega)
    have ht := finite_E₂ K (i+3) (q-1-i)
    rw [hpq] at ht
    change Module.Finite R ((filteredData K (1+q+1)).E₂ (2+(i:ℤ)+2))
    rw [show ((i+3:ℕ):ℤ)+1=2+(i:ℤ)+2 by omega] at ht
    exact ht
  have hzero : E.FC (2-2)=⊥ := filtration_zero K (1+q-1)
  have htop : E.FA (2+(q:ℤ)+1)=⊤ := by
    change filtration K (1+q+1) (2+(q:ℤ)+1)=⊤
    rw [show 2+(q:ℤ)+1=((1+q+1:ℕ):ℤ)+1 by omega]
    exact filtration_top K (1+q+1)
  have : Module.Finite R ((filteredData K (1+q)).E₂ ((1:ℤ)+1)) :=
    E.finite_edge 2 hzero (2+(q:ℤ)+1) htop
  exact Module.Finite.of_surjective (descendedLead K 1 q) (first_descendedLead_surjective K q)
end E2Leading
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ) [Module.Finite R ((K.total c).homology (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R ((row K r).homology p)) :
    Module.Finite R ((row K q).homology 1) := by
  have : Module.Finite R (ConcreteHomology.H (K.total c) (1+q)) :=
    Module.Finite.equiv (ConcreteHomology.iso (K.total c) (1+q)).toLinearEquiv
  have : Module.Finite R (ConcreteHomology.H (E2Leading.row K q) 1) := by
    apply E2Leading.finite_first K q
    intro p r hpr hp
    have := hf p r hpr hp
    exact Module.Finite.equiv (rowHomologyIso K p r).toLinearEquiv
  exact Module.Finite.equiv (rowHomologyIso K 1 q).symm.toLinearEquiv
end TotalFiniteness

end

end OAI
