import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PairTail02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
variable (c : RealCoordinates G n) (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
include hΓ in
omit [IsTopologicalGroup G] in
lemma integerCoordinates_rational : Γ ≤ rationalSubgroup c := by
  intro g hg i
  obtain ⟨z,hz⟩ := (hΓ g).mp hg i
  exact ⟨(z:ℚ),by simpa using hz.symm⟩

include hΓ in
lemma integerCoordinates_discrete : DiscreteTopology Γ := by
  have hopen : IsOpen (⋂ i : Fin n, {g : Γ | |c.coord g.val i| < 1}) := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (((continuous_apply i).comp c.coord.continuous).comp continuous_subtype_val).abs continuous_const
  have heq : (⋂ i : Fin n, {g : Γ | |c.coord g.val i| < 1}) = {1} := by
    ext g
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · intro hg
      apply Subtype.ext
      apply c.coord.injective
      funext i
      change c.coord g.val i = c.coord 1 i
      rw [c.one_coord]
      obtain ⟨z,hz⟩ := (hΓ g.val).mp g.property i
      have hgi := hg i
      rw [hz] at hgi ⊢
      have hz0 : z=0 := by
        have hi : |z| < 1 := by exact_mod_cast hgi
        have := abs_lt.mp hi
        omega
      simp [hz0]
    · rintro rfl
      intro i
      simp [c.one_coord]
  rw [heq] at hopen
  exact discreteTopology_of_isOpen_singleton_one hopen

end RationalLattice
end
end
 

 
section
open scoped commutatorElement
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

 
def coordinateTail (k : ℕ) : Subgroup G where
  carrier := {g | ∀ i : Fin n, i.val < k → c.coord g i = 0}
  one_mem' := fun i _ => c.one_coord i
  mul_mem' := by
    intro g h hg hh i hi
    rw [coord_mul_of_right_zero c g h i (fun j hj => hh j (lt_trans hj hi)),hg i hi,hh i hi]
    ring
  inv_mem' := by
    intro g hg i hi
    have he := coord_mul_of_left_zero c g g⁻¹ i (fun j hj => hg j (lt_trans hj hi))
    rw [mul_inv_cancel,c.one_coord,hg i hi] at he
    linarith

@[simp] lemma mem_coordinateTail (k : ℕ) (g : G) :
    g ∈ coordinateTail c k ↔ ∀ i : Fin n, i.val < k → c.coord g i = 0 := Iff.rfl
lemma coordinateTail_zero : coordinateTail c 0 = ⊤ := by
  ext g
  simp
lemma coordinateTail_end (k : ℕ) (hk : n ≤ k) : coordinateTail c k = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply (Subgroup.mem_bot).mpr
  apply c.coord.injective
  funext i
  rw [c.one_coord]
  exact hg i (lt_of_lt_of_le i.isLt hk)
lemma coordinateTail_antitone : Antitone (coordinateTail c) := by
  intro i j hij g hg a ha
  exact hg a (lt_of_lt_of_le ha hij)

lemma coordinateTail_normal (k : ℕ) : (coordinateTail c k).Normal where
  conj_mem x hx g := by
    intro i hi
    have he := conj_coord_difference c g⁻¹ i (u:=x) (v:=1) (by
      intro j hj
      rw [hx j (lt_trans hj hi),c.one_coord])
    simpa [hx i hi,c.one_coord] using he

 

lemma coordinateTail_commutator (k : ℕ) (g x : G) (hx : x ∈ coordinateTail c k) :
    ⁅g,x⁆ ∈ coordinateTail c (k+1) := by
  intro i hi
  have hxlow : ∀ j : Fin n, j < i → c.coord x j = 0 := by
    intro j hj
    exact hx j (by change j.val < i.val at hj; omega)
  have hilow : ∀ j : Fin n, j < i → c.coord x⁻¹ j = 0 := by
    intro j hj
    exact (coordinateTail c k).inv_mem hx j (by change j.val < i.val at hj; omega)
  have hc := conj_coord_difference c g⁻¹ i (u:=x) (v:=1) (by
    intro j hj
    rw [hxlow j hj,c.one_coord])
  simp only [inv_inv,mul_one,mul_inv_cancel,c.one_coord,sub_zero] at hc
  have hinv := coord_mul_of_left_zero c x x⁻¹ i hxlow
  rw [mul_inv_cancel,c.one_coord] at hinv
  rw [commutatorElement_def,coord_mul_of_right_zero c _ _ i hilow]
  linarith

include c in
theorem nilpotent_of_coordinates : Group.IsNilpotent G := by
  apply (Subgroup.nilpotent_iff_finite_descending_central_series G).mpr
  refine ⟨n,coordinateTail c,⟨coordinateTail_zero c,?_⟩,coordinateTail_end c n le_rfl⟩
  intro x i hx g
  simpa only [commutatorElement_inv] using
    (coordinateTail c (i+1)).inv_mem (coordinateTail_commutator c i g x hx)

variable [IsTopologicalGroup G] (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
include hΓ in
 
omit [IsTopologicalGroup G] in
theorem coordinateTail_compact_reps (k : ℕ) :
    ∃ C : Set G, IsCompact C ∧ C ⊆ coordinateTail c k ∧
      ∀ g ∈ coordinateTail c k, ∃ a ∈ C, a⁻¹*g ∈ Γ := by
  by_cases hk : n ≤ k
  · rw [coordinateTail_end c k hk]
    refine ⟨{1},isCompact_singleton,by simp,?_⟩
    intro g hg
    have hg1 : g=1 := (Subgroup.mem_bot).mp hg
    subst g
    exact ⟨1,by simp,by simp⟩
  · have hk' : k ≤ n := by omega
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hk'
    let T := coordinateTail c k
    let tc := RationalTailCoordinates.tailCoordinates c T (mem_coordinateTail c k)
    let Λ := Γ.comap T.subtype
    have hΛ : ∀ g : T, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, tc.coord g i = z := by
      intro g
      exact RationalTailCoordinates.tailCoordinates_lattice c T (mem_coordinateTail c k) Γ hΓ g
    obtain ⟨C,hC,hr⟩ := compact_reps_of_integerCoordinates tc Λ hΛ
    refine ⟨Subtype.val '' C,hC.image continuous_subtype_val,?_,?_⟩
    · rintro _ ⟨g,hg,rfl⟩
      exact g.property
    · intro g hg
      obtain ⟨a,ha,he⟩ := hr ⟨g,hg⟩
      exact ⟨a.val,⟨a,ha,rfl⟩,he⟩

end RationalLattice
end
end
 

 
section

 

namespace RationalQuotientFunctions
variable {G Y : Type*} [Group G]

 

def cosetLift (Γ : Subgroup G) (f : G → Y)
    (hf : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) : G ⧸ Γ → Y :=
  Quotient.lift f (by
    intro a b h
    have hh := hf a (a⁻¹*b) (QuotientGroup.leftRel_apply.mp h)
    simpa using hh.symm)

@[simp] lemma cosetLift_mk (Γ : Subgroup G) (f : G → Y)
    (hf : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) (g : G) :
    cosetLift Γ f hf (QuotientGroup.mk g) = f g := rfl

variable [TopologicalSpace G] [TopologicalSpace Y]

lemma continuous_cosetLift (Γ : Subgroup G) (f : G → Y)
    (hf : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) (hc : Continuous f) :
    Continuous (cosetLift Γ f hf) :=
  (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr hc

variable (N Γ : Subgroup G) [N.Normal]

omit [TopologicalSpace G] [TopologicalSpace Y] in
 

lemma normal_lift_invariant (f : G → Y)
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g)
    (g : G ⧸ N) (γ : G ⧸ N) (hγ : γ ∈ Γ.map (QuotientGroup.mk' N)) :
    cosetLift N f hN (g*γ) = cosetLift N f hN g := by
  obtain ⟨c,hc,rfl⟩ := hγ
  induction g using Quotient.inductionOn with | h a =>
    exact hΓ a c hc

 

def normalDescend (f : G → Y)
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) :
    ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) → Y :=
  cosetLift _ (cosetLift N f hN) (normal_lift_invariant N Γ f hN hΓ)

omit [TopologicalSpace G] [TopologicalSpace Y] in
@[simp] lemma normalDescend_mk (f : G → Y)
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) (g : G) :
    normalDescend N Γ f hN hΓ
      (QuotientGroup.mk (QuotientGroup.mk' N g)) = f g := rfl

lemma continuous_normalDescend (f : G → Y)
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) (hc : Continuous f) :
    Continuous (normalDescend N Γ f hN hΓ) :=
  continuous_cosetLift _ _ _ (continuous_cosetLift _ _ _ hc)

 

omit [TopologicalSpace G] [TopologicalSpace Y] in
lemma normalDescend_forall (f : G → Y)
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) (P : Y → Prop) :
    (∀ x, P (normalDescend N Γ f hN hΓ x)) ↔ ∀ g, P (f g) := by
  constructor
  · intro h g
    exact h (QuotientGroup.mk (QuotientGroup.mk' N g))
  · intro h x
    induction x using Quotient.inductionOn with | h y =>
      induction y using Quotient.inductionOn with | h g => exact h g

 

theorem existsUnique_normalDescend (f : C(G,Y))
    (hN : ∀ g n, n ∈ N → f (g*n) = f g)
    (hΓ : ∀ g γ, γ ∈ Γ → f (g*γ) = f g) :
    ∃! F : C((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N),Y),
      ∀ g, F (QuotientGroup.mk (QuotientGroup.mk' N g)) = f g := by
  refine ⟨⟨normalDescend N Γ f hN hΓ,
    continuous_normalDescend N Γ f hN hΓ f.continuous⟩,fun _ => rfl,?_⟩
  intro F hF
  ext x
  induction x using Quotient.inductionOn with | h y =>
    induction y using Quotient.inductionOn with | h g => exact hF g

 

def quotientMap : G ⧸ Γ → (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N) :=
  cosetLift Γ (fun g => QuotientGroup.mk (QuotientGroup.mk' N g)) (by
    intro g γ hγ
    rw [map_mul]
    exact QuotientGroup.mk_mul_of_mem _ ⟨γ,hγ,rfl⟩)

lemma continuous_quotientMap : Continuous (quotientMap N Γ) :=
  continuous_cosetLift _ _ _
    (QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk)

omit [TopologicalSpace G] in
lemma quotientMap_surjective : Function.Surjective (quotientMap N Γ) := by
  intro x
  induction x using Quotient.inductionOn with | h y =>
    induction y using Quotient.inductionOn with | h g =>
      exact ⟨QuotientGroup.mk g,rfl⟩

end RationalQuotientFunctions

 

end
end
end
end

end OAI
