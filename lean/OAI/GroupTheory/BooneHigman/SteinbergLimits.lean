import OAI.GroupTheory.BooneHigman.Corners
import OAI.GroupTheory.BooneHigman.MappingTori

namespace OAI

noncomputable section

/-!
Steinberg sequential limits, annihilated kernels, and injective torus maps.
-/

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

theorem transition_injective (hf : Function.Injective f) (i j : ℕ) (hij : i≤j) :
    Function.Injective (transition f i j hij) := by
  change Function.Injective ((f^(j-i) : Monoid.End Q) : Q → Q)
  generalize j-i=n
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    rw [pow_succ']
    exact hf.comp ih

theorem of_injective (hf : Function.Injective f) (i : ℕ) : Function.Injective (of f i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  change of f i x=1 at hx
  obtain ⟨j,hij,he⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => Q) (f:=transition f) ⟨i,x⟩).mp hx
  apply transition_injective f hf i j hij
  simpa only [map_one] using he

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {R : Type*} [Ring R]

abbrev ElementaryGroup (R : Type*) [Ring R] :=
  (matrixMap : Group (Fin 6) R →* (Matrix (Fin 6) (Fin 6) R)ˣ).range

def elementaryQuotient : Group (Fin 6) R →* ElementaryGroup R := matrixMap.rangeRestrict

theorem elementaryQuotient_surjective : Function.Surjective (elementaryQuotient (R:=R)) :=
  MonoidHom.rangeRestrict_surjective _

def correctedUnits (ψ : R →ₙ+* R) := Units.map (correctedMap (matrixNonunitalMap (ι:=Fin 6) ψ))

theorem correctedUnits_injective (ψ : R →ₙ+* R) (hψ : Function.Injective ψ) :
    Function.Injective (correctedUnits ψ) := by
  intro a b he
  apply Units.ext
  apply correctedMap_injective (matrixNonunitalMap ψ) (by
    intro x y hxy
    ext i j
    exact hψ (congrFun (congrFun hxy i) j))
  exact congrArg Units.val he

def elementaryTransition (ψ : R →ₙ+* R) : Monoid.End (ElementaryGroup R) :=
  ((correctedUnits ψ).comp (ElementaryGroup R).subtype).codRestrict (ElementaryGroup R) (by
    intro a
    obtain ⟨z,hz⟩ := a.property
    refine ⟨coefficientMap ψ z,?_⟩
    rw [matrixMap_coefficientMap,hz]
    rfl)

theorem elementaryTransition_injective (ψ : R →ₙ+* R) (hψ : Function.Injective ψ) :
    Function.Injective (elementaryTransition ψ) := by
  intro a b he
  apply Subtype.ext
  exact correctedUnits_injective ψ hψ (congrArg Subtype.val he)

theorem elementary_natural (ψ : R →ₙ+* R) (z : Group (Fin 6) R) :
    elementaryQuotient (coefficientMap ψ z)=elementaryTransition ψ (elementaryQuotient z) := by
  apply Subtype.ext
  exact matrixMap_coefficientMap ψ z

def limitEquivalence (ψ : R →ₙ+* R)
    (hk : ∀ z : Group (Fin 6) R, matrixMap z=1 → coefficientMap ψ z=1) :
    SequentialLimit.Limit (coefficientMap (ι:=Fin 6) ψ) ≃* SequentialLimit.Limit (elementaryTransition ψ) :=
  SequentialLimit.equivalence _ _ elementaryQuotient (elementary_natural ψ) elementaryQuotient_surjective
    (by intro z hz; exact hk z (congrArg Subtype.val hz))

end FiniteAlgebraicEnvelopes.Steinberg
end

namespace FiniteAlgebraicEnvelopes.Steinberg

section
open scoped commutatorElement
variable {R : Type*} [Ring R]

private theorem freshThird (i j : Fin 6) : ∃ k : Fin 6, k≠i ∧ k≠j := by
  have hh : ∃ k ∈ (Finset.univ : Finset (Fin 6)), k∉({i,j} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have hc : ({i,j} : Finset (Fin 6)).card≤2 := by
      simpa using Finset.card_insert_le i {j}
    simpa using (show ({i,j} : Finset (Fin 6)).card<6 by omega)
  simpa using hh

/-- Ring coefficients whose root elements belong to a subgroup form a subring.
The rank-six third index is used in the multiplication step. -/
def coefficientSubring (H : Subgroup (Group (Fin 6) R))
    (h1 : ∀ i j (hij : i≠j), root i j hij (1:R)∈H) : Subring R where
  carrier := {r | ∀ i j (hij : i≠j), root i j hij r∈H}
  zero_mem' := by intro i j hij; rw [root_zero]; exact H.one_mem
  one_mem' := h1
  add_mem' := by
    intro r s hr hs i j hij
    rw [←root_add]
    exact H.mul_mem (hr i j hij) (hs i j hij)
  neg_mem' := by
    intro r hr i j hij
    rw [root_neg]
    exact H.inv_mem (hr i j hij)
  mul_mem' := by
    intro r s hr hs i j hij
    obtain ⟨k,hki,hkj⟩ := freshThird i j
    rw [←root_chain i k j hki.symm hkj hij]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hr i k hki.symm) (hs k j hkj))
      (H.inv_mem (hr i k hki.symm))) (H.inv_mem (hs k j hkj))

abbrev RootIndex := {p : Fin 6 × Fin 6 // p.1≠p.2}

def rootGenerators (S : Set R) : Set (Group (Fin 6) R) :=
  (fun p : RootIndex × R => root p.1.1.1 p.1.1.2 p.1.2 p.2) '' (Set.univ ×ˢ insert 1 S)

theorem rootGenerators_finite {S : Set R} (hS : S.Finite) : (rootGenerators S).Finite :=
  (Set.toFinite (Set.univ : Set RootIndex) |>.prod (hS.insert 1)).image _

theorem root_mem_generators {S : Set R} (i j : Fin 6) (hij : i≠j) {r : R}
    (hr : r∈insert 1 S) : root i j hij r∈rootGenerators S :=
  ⟨(⟨(i,j),hij⟩,r),⟨Set.mem_univ _,hr⟩,rfl⟩

theorem rootGenerators_generate {S : Set R} (hS : Subring.closure S=⊤) :
    Subgroup.closure (rootGenerators S)=⊤ := by
  let H := Subgroup.closure (rootGenerators S)
  have h1 (i j : Fin 6) (hij : i≠j) : root i j hij (1:R)∈H :=
    Subgroup.subset_closure (root_mem_generators i j hij (Set.mem_insert 1 S))
  let C := coefficientSubring H h1
  have hSC : Subring.closure S≤C := Subring.closure_le.mpr (by
    intro r hr i j hij
    exact Subgroup.subset_closure (root_mem_generators i j hij (Set.mem_insert_of_mem 1 hr)))
  have hC (r : R) : r∈C := by rw [hS] at hSC; exact hSC (Subring.mem_top _)
  apply top_unique
  rw [←PresentedGroup.closure_range_of]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨⟨⟨i,j⟩,hij⟩,r⟩,rfl⟩
  exact hC r i j hij

theorem finitelyGenerated_of_ringGenerators {S : Set R} (hS : S.Finite)
    (hgen : Subring.closure S=⊤) : _root_.Group.FG (Group (Fin 6) R) :=
  _root_.Group.fg_iff.mpr ⟨rootGenerators S,rootGenerators_generate hgen,rootGenerators_finite hS⟩

variable [Algebra (ZMod 2) R]

theorem ringGenerators_of_algebraGenerators {S : Set R} (hS : Algebra.adjoin (ZMod 2) S=⊤) :
    Subring.closure S=⊤ := by
  let C : Subalgebra (ZMod 2) R := {
    toSubsemiring := (Subring.closure S).toSubsemiring
    algebraMap_mem' := by
      intro c
      have he : c=0 ∨ c=1 := by revert c; decide
      rcases he with rfl|rfl <;> simp }
  have hle : Algebra.adjoin (ZMod 2) S≤C := Algebra.adjoin_le (fun r hr => Subring.subset_closure hr)
  apply top_unique
  intro r hr
  have hc : r∈C := hle (by rw [hS]; trivial)
  exact hc

end

open scoped commutatorElement
variable {R : Type*} [Ring R]

private theorem thirdIndex (i j : Fin 6) : ∃ k : Fin 6, k≠i ∧ k≠j := by
  have hh : ∃ k ∈ (Finset.univ : Finset (Fin 6)), k∉({i,j} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have hc : ({i,j} : Finset (Fin 6)).card≤2 := by simpa using Finset.card_insert_le i {j}
    simpa using (show ({i,j} : Finset (Fin 6)).card<6 by omega)
  simpa using hh

variable (r : R → R → Prop)
def ringRelators : Set (Group (Fin 6) R) :=
  {z | ∃ (i j : Fin 6) (hij : i≠j) (a b : R), r a b ∧ z=root i j hij a*(root i j hij b)⁻¹}

def ringKernel : Subgroup (Group (Fin 6) R) := Subgroup.normalClosure (ringRelators r)
instance : (ringKernel r).Normal := Subgroup.normalClosure_normal
abbrev RingQuotientGroup := Group (Fin 6) R ⧸ ringKernel r

def quotientRoot (i j : Fin 6) (hij : i≠j) (a : R) : RingQuotientGroup r :=
  QuotientGroup.mk' (ringKernel r) (root i j hij a)

@[simp] theorem quotientRoot_add (i j : Fin 6) (hij : i≠j) (a b : R) :
    quotientRoot r i j hij a * quotientRoot r i j hij b=quotientRoot r i j hij (a+b) := by
  rw [quotientRoot,quotientRoot,←map_mul,root_add]
  rfl

theorem quotientRoot_chain (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    ⁅quotientRoot r i j hij a,quotientRoot r j k hjk b⁆=quotientRoot r i k hik (a*b) := by
  simp only [quotientRoot,←map_commutatorElement]
  rw [root_chain i j k hij hjk hik]

theorem quotientRoot_rel {a b : R} (hr : r a b) (i j : Fin 6) (hij : i≠j) :
    quotientRoot r i j hij a=quotientRoot r i j hij b := by
  apply mul_inv_eq_one.mp
  change QuotientGroup.mk' (ringKernel r) (root i j hij a)*
    (QuotientGroup.mk' (ringKernel r) (root i j hij b))⁻¹=1
  rw [←map_inv,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure ⟨i,j,hij,a,b,hr,rfl⟩

theorem quotientRoot_congr {a b : R} (hr : RingQuot.Rel r a b) :
    ∀ (i j : Fin 6) (hij : i≠j), quotientRoot r i j hij a=quotientRoot r i j hij b := by
  induction hr with
  | of hr => exact quotientRoot_rel r hr
  | add_left hr ih =>
    intro i j hij
    rw [←quotientRoot_add,←quotientRoot_add,ih i j hij]
  | mul_left hr ih =>
    intro i j hij
    obtain ⟨k,hki,hkj⟩ := thirdIndex i j
    rw [←quotientRoot_chain r i k j hki.symm hkj hij,
      ←quotientRoot_chain r i k j hki.symm hkj hij,ih i k hki.symm]
  | mul_right hr ih =>
    intro i j hij
    obtain ⟨k,hki,hkj⟩ := thirdIndex i j
    rw [←quotientRoot_chain r i k j hki.symm hkj hij,
      ←quotientRoot_chain r i k j hki.symm hkj hij,ih k j hkj]

def ringQuotRoot (i j : Fin 6) (hij : i≠j) (a : RingQuot r) : RingQuotientGroup r :=
  Quot.lift (quotientRoot r i j hij) (fun _ _ h => quotientRoot_congr r h i j hij) a.toQuot

@[simp] theorem ringQuotRoot_mk (i j : Fin 6) (hij : i≠j) (a : R) :
    ringQuotRoot r i j hij (RingQuot.mkRingHom r a)=quotientRoot r i j hij a := by
  rw [RingQuot.mkRingHom_def]
  rfl

theorem ringQuotRoot_add (i j : Fin 6) (hij : i≠j) (a b : RingQuot r) :
    ringQuotRoot r i j hij a * ringQuotRoot r i j hij b=ringQuotRoot r i j hij (a+b) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [←map_add,ringQuotRoot_mk,ringQuotRoot_mk,ringQuotRoot_mk,quotientRoot_add]

theorem ringQuotRoot_chain (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : RingQuot r) :
    ⁅ringQuotRoot r i j hij a,ringQuotRoot r j k hjk b⁆=ringQuotRoot r i k hik (a*b) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [←map_mul,ringQuotRoot_mk,ringQuotRoot_mk,ringQuotRoot_mk,quotientRoot_chain]

theorem ringQuotRoot_distant (i j k l : Fin 6) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : RingQuot r) :
    ⁅ringQuotRoot r i j hij a,ringQuotRoot r k l hkl b⁆=1 := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [ringQuotRoot_mk,ringQuotRoot_mk]
  exact ((root_distant i j k l hij hkl hil hjk a b).map (QuotientGroup.mk' (ringKernel r))).commutator_eq

def quotientBackward : Group (Fin 6) (RingQuot r) →* RingQuotientGroup r :=
  PresentedGroup.toGroup (f:=fun z : Generator (Fin 6) (RingQuot r) =>
    ringQuotRoot r z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive i j hij a b =>
        simp only [map_mul,map_inv,freeRoot,FreeGroup.lift_apply_of]
        rw [ringQuotRoot_add,mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul,map_inv,map_commutatorElement,freeRoot,FreeGroup.lift_apply_of]
        rw [ringQuotRoot_chain r i j k hij hjk hik,mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement,freeRoot,FreeGroup.lift_apply_of]
        exact ringQuotRoot_distant r i j k l hij hkl hil hjk a b)

@[simp] theorem quotientBackward_root (i j : Fin 6) (hij : i≠j) (a : RingQuot r) :
    quotientBackward r (root i j hij a)=ringQuotRoot r i j hij a := PresentedGroup.toGroup.of _

def quotientForward : RingQuotientGroup r →* Group (Fin 6) (RingQuot r) :=
  QuotientGroup.lift (ringKernel r) (coefficientMap (RingQuot.mkRingHom r).toNonUnitalRingHom) (by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨i,j,hij,a,b,hab,rfl⟩
    change coefficientMap _ (root i j hij a*(root i j hij b)⁻¹)=1
    rw [map_mul,map_inv,coefficientMap_root,coefficientMap_root]
    change root i j hij (RingQuot.mkRingHom r a)*(root i j hij (RingQuot.mkRingHom r b))⁻¹=1
    rw [RingQuot.mkRingHom_rel hab,mul_inv_cancel])

@[simp] theorem quotientForward_quotientRoot (i j : Fin 6) (hij : i≠j) (a : R) :
    quotientForward r (quotientRoot r i j hij a)=root i j hij (RingQuot.mkRingHom r a) :=
  coefficientMap_root _ _ _ _ _

theorem quotientForward_backward : (quotientForward r).comp (quotientBackward r)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  change quotientForward r (quotientBackward r (root i j hij (RingQuot.mkRingHom r a)))=_
  rw [quotientBackward_root,ringQuotRoot_mk,quotientForward_quotientRoot]
  rfl

theorem quotientBackward_forward : (quotientBackward r).comp (quotientForward r)=MonoidHom.id _ := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (ringKernel r)) |>.mp
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
  change quotientBackward r (quotientForward r (quotientRoot r i j hij a))=quotientRoot r i j hij a
  rw [quotientForward_quotientRoot,quotientBackward_root,ringQuotRoot_mk]

def ringQuotEquivalence : RingQuotientGroup r ≃* Group (Fin 6) (RingQuot r) :=
  { quotientForward r with
    invFun := quotientBackward r
    left_inv := DFunLike.congr_fun (quotientBackward_forward r)
    right_inv := DFunLike.congr_fun (quotientForward_backward r) }

theorem ringRelators_finite (hr : {p : R×R | r p.1 p.2}.Finite) : (ringRelators r).Finite := by
  have he : ringRelators r=(fun p : RootIndex×(R×R) =>
    root p.1.1.1 p.1.1.2 p.1.2 p.2.1*(root p.1.1.1 p.1.1.2 p.1.2 p.2.2)⁻¹) ''
    (Set.univ ×ˢ {p : R×R | r p.1 p.2}) := by
    ext z
    constructor
    · rintro ⟨i,j,hij,a,b,hab,rfl⟩
      exact ⟨(⟨(i,j),hij⟩,(a,b)),⟨Set.mem_univ _,hab⟩,rfl⟩
    · rintro ⟨⟨⟨⟨i,j⟩,hij⟩,⟨a,b⟩⟩,⟨_,hab⟩,rfl⟩
      exact ⟨i,j,hij,a,b,hab,rfl⟩
  rw [he]
  exact ((Set.toFinite (Set.univ : Set RootIndex)).prod hr).image _

/-- Finite ring equations require only finitely many additional Steinberg relators. -/
theorem ringQuot_finitelyPresented (hr : {p : R×R | r p.1 p.2}.Finite)
    [_root_.Group.IsFinitelyPresented (Group (Fin 6) R)] :
    _root_.Group.IsFinitelyPresented (Group (Fin 6) (RingQuot r)) := by
  have : _root_.Group.IsFinitelyPresented (RingQuotientGroup r) :=
    _root_.Group.IsFinitelyPresented.quotient (ringKernel r) ⟨ringRelators r,ringRelators_finite r hr,rfl⟩
  exact _root_.Group.IsFinitelyPresented.equiv (ringQuotEquivalence r)

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
