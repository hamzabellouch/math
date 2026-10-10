import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentPureAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def completedPureUnit : (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (PowerSeries.C (R:=HahnSeries ℤ (Torus v Ω))) (pureLaurentUnit v Ω hΩ p)
lemma completed_expand_pure
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (completedPureAction v _ _ f)=
      innerHom (completedPureUnit v Ω hΩ p) (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  apply PowerSeries.ext
  intro d
  change expandFiber v Ω hΩ k p
    (coeff d (completedPureAction v (complementOmega k Ω) (complementAlpha k p Ω) f))=
    coeff d (PowerSeries.C (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
      PowerSeries.map (expandFiber v Ω hΩ k p) f*
        PowerSeries.C (↑((pureLaurentUnit v Ω hΩ p)⁻¹):HahnSeries ℤ (Torus v Ω)))
  change expandFiber v Ω hΩ k p
    (coeff d (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f))=_
  rw [coeff_map,coeff_mul_C,coeff_C_mul,coeff_map]
  exact expand_pure_conjugate v Ω hΩ p k hq (coeff d f)
lemma innerHom_one {A : Type*} [Ring A] (a : A) : innerHom (1:Aˣ) a=a := by
  simp [innerHom]
lemma innerHom_mul {A : Type*} [Ring A] (u w : Aˣ) (a : A) :
    innerHom (u*w) a=innerHom u (innerHom w a) := by
  simp [innerHom,mul_assoc]
lemma innerHom_inv_cancel {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u⁻¹ (innerHom u a)=a := by
  rw [←innerHom_mul,inv_mul_cancel,innerHom_one]
lemma innerHom_cancel_inv {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u (innerHom u⁻¹ a)=a := by
  rw [←innerHom_mul,mul_inv_cancel,innerHom_one]
lemma completed_expand_pure_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) ((completedPureAction v _ _).symm f)=
      innerHom (completedPureUnit v Ω hΩ p)⁻¹ (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  have H:=completed_expand_pure v Ω hΩ k p hq ((completedPureAction v _ _).symm f)
  rw [RingEquiv.apply_symm_apply] at H
  have HH:=congrArg (innerHom (completedPureUnit v Ω hΩ p)⁻¹) H
  rw [innerHom_inv_cancel] at HH
  exact HH.symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def oldUnitExpand (u : (biSupportedSubring v Ω δ k)ˣ) :
    (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (oldLaurentHom v Ω δ k) u

def boundedRationalUnit (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val) :
    (PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))ˣ where
  val:=rationalRegrade v Ω hΩ k p hp δ B u.val.val
  inv:=rationalRegrade v Ω hΩ k p hp δ B u.inv.val
  val_inv:=by
    rw [←rationalRegrade_mul v Ω hΩ k p hp δ B hf hg]
    have H:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.val_inv
    change u.val.val*u.inv.val=1 at H
    rw [H,rationalRegrade_one]
  inv_val:=by
    rw [←rationalRegrade_mul v Ω hΩ k p hp δ B hg hf]
    have H:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.inv_val
    change u.inv.val*u.val.val=1 at H
    rw [H,rationalRegrade_one]
lemma boundedUnit_expansion (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val) :
    Units.map (PowerSeries.map (expandFiber v Ω hΩ k p))
      (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg)=oldUnitExpand v Ω δ k u := by
  apply Units.ext
  change PowerSeries.map (expandFiber v Ω hΩ k p)
    (rationalRegrade v Ω hΩ k p hp δ B u.val.val)=oldLaurent v Ω δ k u.val.val
  exact rational_old_square v Ω hΩ k p hp δ B u.val.property hf

variable (hδ : δ p=0)
def oldPureUnit : (biSupportedSubring v Ω δ k)ˣ where
  val:=⟨raySeries v Ω p (shiftedElementary v 0),pure_biSupported v Ω δ k p hδ hp _⟩
  inv:=⟨raySeries v Ω p (shiftedElementary v 0)⁻¹,pure_biSupported v Ω δ k p hδ hp _⟩
  val_inv:=Subtype.ext (rayUnit v Ω p (hΩ p) _ (shiftedElementary_constant v 0)).val_inv
  inv_val:=Subtype.ext (rayUnit v Ω p (hΩ p) _ (shiftedElementary_constant v 0)).inv_val
lemma oldPureUnit_expansion :
    oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)=completedPureUnit v Ω hΩ p := by
  apply Units.ext
  exact oldLaurent_pure v Ω hΩ δ k p hδ hp _
lemma map_innerHom {A B : Type*} [Ring A] [Ring B] (F : A →+* B) (u : Aˣ) (x : A) :
    F (innerHom u x)=innerHom (Units.map F u) (F x) := by
  simp [innerHom]
lemma bounded_conjugation_expansion (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p)
      (innerHom (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg) f)=
      innerHom (oldUnitExpand v Ω δ k u) (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  rw [map_innerHom,boundedUnit_expansion]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

inductive ComparisonCrossing where
  | bounded (u : (biSupportedSubring v Ω δ k)ˣ)
      (forward_bound : RegradeBound v Ω δ B u.val.val)
      (inverse_bound : RegradeBound v Ω δ B u.inv.val)
  | pure (forward : Bool)

def comparisonOld : ComparisonCrossing v Ω δ k B → (biSupportedSubring v Ω δ k)ˣ
  | .bounded u _ _=>u
  | .pure true=>oldPureUnit v Ω hΩ δ k p hp hδ
  | .pure false=>(oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹

def comparisonAction (c : ComparisonCrossing v Ω δ k B) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) →+*
      PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  match c with
  | .bounded u hf hg=>innerHom (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg)
  | .pure true=>(completedPureAction v _ _).toRingHom
  | .pure false=>(completedPureAction v _ _).symm.toRingHom
lemma comparison_expansion (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (c : ComparisonCrossing v Ω δ k B)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (comparisonAction v Ω hΩ δ k p hp B c f)=
      innerHom (oldUnitExpand v Ω δ k (comparisonOld v Ω hΩ δ k p hp hδ B c))
        (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  cases c with
  | bounded u hf hg=>exact bounded_conjugation_expansion v Ω hΩ δ k p hp B u hf hg f
  | pure b=>
    cases b
    · change _=innerHom (oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹) _
      have H : oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹=
          (completedPureUnit v Ω hΩ p)⁻¹ := by
        rw [oldUnitExpand,map_inv,←oldPureUnit_expansion v Ω hΩ δ k p hp hδ]
        rfl
      rw [H]
      exact completed_expand_pure_inverse v Ω hΩ k p hq f
    · change _=innerHom (oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)) _
      rw [oldPureUnit_expansion]
      exact completed_expand_pure v Ω hΩ k p hq f

def comparisonWordOld (l : List (ComparisonCrossing v Ω δ k B)) :
    (biSupportedSubring v Ω δ k)ˣ := (l.map (comparisonOld v Ω hΩ δ k p hp hδ B)).prod

def comparisonWordAction (l : List (ComparisonCrossing v Ω δ k B))
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :=
  l.foldr (fun c a=>comparisonAction v Ω hΩ δ k p hp B c a) f
lemma comparisonWord_expansion (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (l : List (ComparisonCrossing v Ω δ k B))
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (comparisonWordAction v Ω hΩ δ k p hp B l f)=
      innerHom (oldUnitExpand v Ω δ k (comparisonWordOld v Ω hΩ δ k p hp hδ B l))
        (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  induction l with
  | nil=>simp [comparisonWordAction,comparisonWordOld,oldUnitExpand,innerHom_one]
  | cons c l ih=>
    change PowerSeries.map (expandFiber v Ω hΩ k p)
      (comparisonAction v Ω hΩ δ k p hp B c (comparisonWordAction v Ω hΩ δ k p hp B l f))=_
    rw [comparison_expansion v Ω hΩ δ k p hp hδ B hq,ih]
    change _=innerHom (oldUnitExpand v Ω δ k
      (comparisonOld v Ω hΩ δ k p hp hδ B c*comparisonWordOld v Ω hΩ δ k p hp hδ B l)) _
    simp only [oldUnitExpand,map_mul,innerHom_mul]

lemma comparisonWord_loop (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (l : List (ComparisonCrossing v Ω δ k B))
    (hloop : comparisonWordOld v Ω hΩ δ k p hp hδ B l=1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    comparisonWordAction v Ω hΩ δ k p hp B l f=f := by
  apply completed_expandFiber_injective v Ω hΩ k p hp
  rw [comparisonWord_expansion v Ω hΩ δ k p hp hδ B hq,hloop,oldUnitExpand,map_one,innerHom_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
