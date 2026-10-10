import Mathlib

namespace OAI



section
namespace TorsionFreeZeroDivisors.FreeActionNorm
open scoped Classical BigOperators
open CategoryTheory
noncomputable section
variable {H X : Type} [CommGroup H] [MulAction H X] [IsCancelSMul H X]
abbrev Orbit := Quotient (MulAction.orbitRel H X)
def orbitMap (p : Orbit (H:=H) (X:=X) × H) : X := p.2 • p.1.out
omit [IsCancelSMul H X] in
lemma orbit_class (h : H) (x : X) : (Quotient.mk'' (h • x) : Orbit (H:=H))=Quotient.mk'' x := by
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨h,rfl⟩
lemma orbitMap_bijective : Function.Bijective (orbitMap (H:=H) (X:=X)) := by
  constructor
  · rintro ⟨j,h⟩ ⟨k,g⟩ he
    have hjk : j=k := by
      have := congrArg (fun x=>(Quotient.mk'' x : Orbit (H:=H))) he
      simpa only [orbitMap,orbit_class,Quotient.out_eq'] using this
    subst k
    exact Prod.ext rfl (IsCancelSMul.right_cancel h g j.out he)
  · intro x
    have hx : x∈MulAction.orbit H (Quotient.mk'' x : Orbit (H:=H)).out := by
      exact (MulAction.orbitRel_apply).mp (Quotient.exact (Quotient.out_eq' (Quotient.mk'' x : Orbit (H:=H))).symm)
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨⟨Quotient.mk'' x,h⟩,hh⟩
def orbitEquiv : Orbit (H:=H) (X:=X) × H ≃ X := Equiv.ofBijective orbitMap orbitMap_bijective
@[simp] lemma orbitEquiv_apply (j : Orbit (H:=H) (X:=X)) (h : H) : orbitEquiv (j,h)=h • j.out := rfl

def act (h : H) : (X→₀ℤ)≃+(X→₀ℤ) := Finsupp.domCongr (MulAction.toPerm h)
omit [IsCancelSMul H X] in
@[simp] lemma act_apply (h : H) (x : X→₀ℤ) (a : X) : act h x a=x (h⁻¹ • a) := rfl

def coords : (X→₀ℤ)≃+(Orbit (H:=H) (X:=X)→₀MonoidAlgebra ℤ H) :=
  ((Finsupp.domCongr orbitEquiv.symm).trans Finsupp.curryAddEquiv).trans
    (Finsupp.mapRange.addEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toAddEquiv)
@[simp] lemma coords_coeff (x : X→₀ℤ) (j : Orbit (H:=H) (X:=X)) (h : H) :
    ((coords x) j).coeff h=x (h • j.out) := rfl
lemma coords_act (h : H) (x : X→₀ℤ) (j : Orbit (H:=H) (X:=X)) :
    coords (act h x) j=(Representation.leftRegular ℤ H h) (coords x j) := by
  ext g
  simp only [coords_coeff,act_apply,←mul_smul,Representation.coeff_ofMulAction]
  rfl
variable [Fintype H]
def norm (x : X→₀ℤ) : X→₀ℤ := ∑h : H,act h x
lemma coords_norm (x : X→₀ℤ) (j : Orbit (H:=H) (X:=X)) :
    coords (norm (H:=H) x) j=(Rep.leftRegular ℤ H).norm.hom (coords x j) := by
  simp only [norm,map_sum,Finsupp.finsetSum_apply,coords_act]
  simp [Rep.norm,Representation.norm,Rep.leftRegular]
lemma invariant_norm (g : H) (hg : ∀h,h∈Subgroup.zpowers g) (x : X→₀ℤ) (hx : act g x=x) :
    ∃y : X→₀ℤ,norm (H:=H) y=x := by
  let f := (Rep.leftRegular ℤ H).norm.hom.toLinearMap
  have hxj (j : Orbit (H:=H) (X:=X)) : coords x j∈Set.range f := by
    change coords x j∈LinearMap.range f
    rw [Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub ℤ g hg]
    have he := congrArg (fun t=>coords t j) hx
    rw [coords_act] at he
    simpa only [LinearMap.mem_ker,Representation.IntertwiningMap.toLinearMap_apply,
      Rep.sub_hom,Representation.IntertwiningMap.coe_sub,Pi.sub_apply,Rep.applyAsHom,Rep.hom_ofHom,Representation.IntertwiningMap.coe_mk,
      Rep.hom_id,Representation.IntertwiningMap.id_apply,sub_eq_zero] using he
  have hm : coords x∈Set.range (Finsupp.mapRange f f.map_zero) := by
    rw [Finsupp.range_mapRange]
    exact hxj
  obtain ⟨z,hz⟩ := hm
  refine ⟨(coords (H:=H) (X:=X)).symm z,(coords (H:=H) (X:=X)).injective ?_⟩
  apply Finsupp.ext
  intro j
  rw [coords_norm,coords.apply_symm_apply]
  exact congrArg (fun y=>y j) hz
lemma kernel_norm (g : H) (hg : ∀h,h∈Subgroup.zpowers g) (x : X→₀ℤ) (hx : norm (H:=H) x=0) :
    ∃y : X→₀ℤ,act g y-y=x := by
  let f := (Rep.applyAsHom (Rep.leftRegular ℤ H) g-𝟙 _).hom.toLinearMap
  have hxj (j : Orbit (H:=H) (X:=X)) : coords x j∈Set.range f := by
    change coords x j∈LinearMap.range f
    rw [Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm ℤ g hg]
    have he := congrArg (fun t=>coords t j) hx
    simpa only [coords_norm,map_zero,Finsupp.zero_apply,LinearMap.mem_ker,
      Representation.IntertwiningMap.toLinearMap_apply] using he
  have hm : coords x∈Set.range (Finsupp.mapRange f f.map_zero) := by
    rw [Finsupp.range_mapRange]
    exact hxj
  obtain ⟨z,hz⟩ := hm
  refine ⟨(coords (H:=H) (X:=X)).symm z,(coords (H:=H) (X:=X)).injective ?_⟩
  apply Finsupp.ext
  intro j
  rw [map_sub,Finsupp.sub_apply,coords_act,coords.apply_symm_apply]
  exact congrArg (fun y=>y j) hz
end
end TorsionFreeZeroDivisors.FreeActionNorm


end



end OAI
