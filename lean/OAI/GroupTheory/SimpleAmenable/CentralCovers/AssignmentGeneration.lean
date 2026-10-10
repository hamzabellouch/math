import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.DirectFactors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CanonicalSectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AssignmentGeneration
open scoped commutatorElement
variable {E Ω : Type*} [Group E]

theorem sectorMask_inter_commutator (U V : Set Ω) (s t : E) :
    sectorMask (U ∩ V) ⁅s,t⁆ = ⁅sectorMask U s,sectorMask V t⁆ := by
  classical
  ext ω
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;>
    simp [sectorMask, hu, hv, commutatorElement_def]

theorem sectorMask_complement (U : Set Ω) (s : E) :
    sectorMask Uᶜ s = sectorMask Set.univ s * (sectorMask U s)⁻¹ := by
  classical
  ext ω
  by_cases hu : ω ∈ U <;> simp [sectorMask, hu]

def SectorAvailable (K : Subgroup (Ω → E)) (U : Set Ω) : Prop :=
  ∀ s, sectorMask U s ∈ K

theorem sectorAvailable_inter [Group.IsPerfect E] (K : Subgroup (Ω → E))
    {U V : Set Ω} (hU : SectorAvailable K U) (hV : SectorAvailable K V) :
    SectorAvailable K (U ∩ V) := by
  let L := K.comap (sectorMask (U ∩ V))
  have hL : commutator E ≤ L := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro s _ t _
    change sectorMask (U ∩ V) ⁅s,t⁆ ∈ K
    rw [sectorMask_inter_commutator]
    exact Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator (hU s) (hV t))
  intro s
  exact hL (Group.IsPerfect.commutator_eq_top (G := E) ▸ Subgroup.mem_top s)

theorem sectorAvailable_compl (K : Subgroup (Ω → E))
    (hwhole : SectorAvailable K Set.univ) {U : Set Ω} (hU : SectorAvailable K U) :
    SectorAvailable K Uᶜ := by
  intro s
  rw [sectorMask_complement]
  exact K.mul_mem (hwhole s) (K.inv_mem (hU s))

theorem sectorAvailable_finsetInter [Group.IsPerfect E] {ι : Type*}
    (K : Subgroup (Ω → E)) (hwhole : SectorAvailable K Set.univ)
    (U : ι → Set Ω) (S : Finset ι) (hU : ∀ i ∈ S, SectorAvailable K (U i)) :
    SectorAvailable K (⋂ i ∈ S, U i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hwhole
  | @insert i S hi ih =>
    rw [Finset.set_biInter_insert]
    exact sectorAvailable_inter K (hU i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hU j (Finset.mem_insert_of_mem hj)))

theorem assignment_group_generated [Group.IsPerfect E] [Finite Ω]
    {ι : Type*} [Finite ι] (U : ι → Set Ω)
    (hsep : ∀ ω ν : Ω, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (K : Subgroup (Ω → E)) (hwhole : SectorAvailable K Set.univ)
    (hU : ∀ i, SectorAvailable K (U i)) : K = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  have hsingle (ω : Ω) : SectorAvailable K {ω} := by
    let V : ι → Set Ω := fun i => if ω ∈ U i then U i else (U i)ᶜ
    have hV (i : ι) : SectorAvailable K (V i) := by
      dsimp [V]
      split_ifs
      · exact hU i
      · exact sectorAvailable_compl K hwhole (hU i)
    have heq : (⋂ i ∈ Finset.univ, V i) = {ω} := by
      ext ν
      simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_singleton_iff]
      constructor
      · intro hν
        apply hsep ν ω
        intro i
        have ht := hν i
        by_cases hi : ω ∈ U i <;> simp_all [V]
      · intro hνω i
        subst ν
        by_cases hi : ω ∈ U i <;> simp [V, hi]
    rw [← heq]
    exact sectorAvailable_finsetInter K hwhole V Finset.univ (fun i _ => hV i)
  apply top_unique
  intro f _
  apply Subgroup.pi_mem_of_mulSingle_mem f
  intro ω
  convert hsingle ω (f ω) using 1
  ext ν
  by_cases h : ν = ω
  · subst ν
    simp
  · simp [sectorMask, h]

end AssignmentGeneration

section FiniteDirectRefinement
variable {G : Type*} [Group G]

namespace CommutingFactors
variable {A B C D : Subgroup G}

noncomputable def projectLeft (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : G →* G :=
  A.subtype.comp ((MonoidHom.fst A B).comp (h.productEquiv hz).symm.toMonoidHom)

@[simp] theorem projectLeft_mem (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : G) : h.projectLeft hz x ∈ A :=
  ((h.productEquiv hz).symm x).1.property

theorem projectLeft_factors (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    h.projectLeft hz (a*b) = a := by
  change (((h.productEquiv hz).symm (a*b)).1 : G) = a
  have hh : (h.productEquiv hz).symm (a*b) = (⟨a,ha⟩,⟨b,hb⟩) := by
    apply (h.productEquiv hz).injective
    simp only [MulEquiv.apply_symm_apply, productEquiv_apply]
  rw [hh]

theorem projectLeft_fix (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {a : G} (ha : a ∈ A) : h.projectLeft hz a = a := by
  simpa using h.projectLeft_factors hz ha B.one_mem

theorem projectLeft_kill (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {b : G} (hb : b ∈ B) : h.projectLeft hz b = 1 := by
  simpa using h.projectLeft_factors hz A.one_mem hb

theorem projectLeft_split (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : G) :
    x = h.projectLeft hz x * h.symm.projectLeft hz x := by
  obtain ⟨a,ha,b,hb,rfl⟩ := h.cover x
  rw [h.projectLeft_factors hz ha hb]
  rw [(h.commute a ha b hb).eq, h.symm.projectLeft_factors hz hb ha]
  exact (h.commute a ha b hb).eq.symm

theorem projectLeft_preserves (h : CommutingFactors A B) (k : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) {x : G} (hx : x ∈ C) : h.projectLeft hz x ∈ C := by
  apply k.mem_left_of_commute_right hz
  intro y hy
  apply h.left_component_commutes hz (h.projectLeft_mem hz x)
    (h.symm.projectLeft_mem hz x)
  rw [← h.projectLeft_split hz x]
  exact k.commute x hx y hy

theorem projectLeft_comp_commute (h : CommutingFactors A B) (k : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) :
    (h.projectLeft hz).comp (k.projectLeft hz) =
      (k.projectLeft hz).comp (h.projectLeft hz) := by
  ext x
  obtain ⟨a,ha,b,hb,rfl⟩ := h.cover x
  simp only [MonoidHom.comp_apply, map_mul]
  rw [h.projectLeft_fix hz ha, h.projectLeft_kill hz hb, map_one, mul_one,
    h.projectLeft_fix hz (k.projectLeft_preserves h hz ha),
    h.projectLeft_kill hz (k.projectLeft_preserves h.symm hz hb), mul_one]

end CommutingFactors

def assignmentFactor {ι : Type*} (A : ι → Subgroup G) (S : Finset ι) : Subgroup G :=
  ⨅ i ∈ S, A i

theorem projectLeft_mem_assignmentFactor {ι : Type*}
    (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    {C D : Subgroup G} (k : CommutingFactors C D) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) {x : G} (hx : x ∈ assignmentFactor A S) :
    k.projectLeft hz x ∈ assignmentFactor A S := by
  simp only [assignmentFactor, Subgroup.mem_iInf] at hx ⊢
  intro i hi
  exact k.projectLeft_preserves (h i) hz (hx i hi)

theorem split_assignmentFactor {ι : Type*}
    (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    {C D : Subgroup G} (k : CommutingFactors C D) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) {x : G} (hx : x ∈ assignmentFactor A S) :
    ∃ c ∈ assignmentFactor A S ⊓ C, ∃ d ∈ assignmentFactor A S ⊓ D, x = c*d := by
  refine ⟨k.projectLeft hz x, ⟨?_,k.projectLeft_mem hz x⟩,
    k.symm.projectLeft hz x, ⟨?_,k.symm.projectLeft_mem hz x⟩,k.projectLeft_split hz x⟩
  · exact projectLeft_mem_assignmentFactor A B h k hz S hx
  · exact projectLeft_mem_assignmentFactor A B h k.symm hz S hx

def refinedFactor {ι : Type*} (A B : ι → Subgroup G) (S : Finset ι)
    (σ : ι → Bool) : Subgroup G :=
  assignmentFactor (fun i => if σ i then A i else B i) S

theorem simultaneous_refinement {ι : Type*} (A B : ι → Subgroup G)
    (h : ∀ i, CommutingFactors (A i) (B i)) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) : (⨆ σ : ι → Bool, refinedFactor A B S σ) = ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [refinedFactor, assignmentFactor]
  | @insert i S hi ih =>
    apply top_unique
    rw [← ih]
    apply iSup_le
    intro σ x hx
    have hp (j : ι) : CommutingFactors
        (if σ j then A j else B j) (if σ j then B j else A j) := by
      cases hs : σ j
      · simpa only [hs, Bool.false_eq_true, ↓reduceIte] using (h j).symm
      · simpa only [hs, ↓reduceIte] using h j
    obtain ⟨c,hc,d,hd,rfl⟩ := split_assignmentFactor
      (fun j => if σ j then A j else B j) (fun j => if σ j then B j else A j)
      hp (h i) hz S hx
    have hm (b : Bool) {z : G}
        (hS : z ∈ refinedFactor A B S σ) (hzi : z ∈ if b then A i else B i) :
        z ∈ refinedFactor A B (insert i S) (Function.update σ i b) := by
      simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf] at hS ⊢
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using hzi
      · have hji : j ≠ i := by
          intro heq
          subst j
          exact hi hj
        simpa only [Function.update_of_ne hji] using hS j hj
    apply Subgroup.mul_mem
    · exact Subgroup.mem_iSup_of_mem (Function.update σ i true) (hm true hc.1 hc.2)
    · exact Subgroup.mem_iSup_of_mem (Function.update σ i false) (hm false hd.1 hd.2)

theorem refinedFactor_commute {ι : Type*} [Fintype ι] (A B : ι → Subgroup G)
    (h : ∀ i, CommutingFactors (A i) (B i)) {σ τ : ι → Bool} (hστ : σ ≠ τ)
    {x y : G} (hx : x ∈ refinedFactor A B Finset.univ σ)
    (hy : y ∈ refinedFactor A B Finset.univ τ) : Commute x y := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hστ
  simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf, Finset.mem_univ,
    forall_const] at hx hy
  specialize hx i
  specialize hy i
  cases hs : σ i <;> cases ht : τ i <;> simp_all
  · exact ((h i).commute y hy x hx).symm
  · exact (h i).commute x hx y hy

theorem commuting_factors_independent {ι : Type*} (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥) : iSupIndep F := by
  classical
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  have hrest : (⨆ j, ⨆ (_ : j ≠ i), F j) ≤ Subgroup.centralizer (F i : Set G) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hji y hy
    exact Subgroup.mem_centralizer_iff.mpr fun z hz' => (hcomm hji y z hy hz').eq.symm
  have hself : x ∈ Subgroup.centralizer (F i : Set G) := hrest hx.2
  have hall : (⨆ j, F j) ≤ Subgroup.centralizer {x} := by
    apply iSup_le
    intro j y hy
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz'
    have hzx : z = x := Set.mem_singleton_iff.mp hz'
    subst z
    by_cases hji : j = i
    · subst j
      exact (Subgroup.mem_centralizer_iff.mp hself y hy).symm
    · exact (hcomm hji y x hy hx.1).eq.symm
  have hcenter : x ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy := hall (hgenerate ▸ Subgroup.mem_top y)
    exact (Subgroup.mem_centralizer_iff.mp hy x (Set.mem_singleton x)).symm
  simpa only [hz, Subgroup.mem_bot] using hcenter

noncomputable def commutingFactorsEquiv {ι : Type*} [Fintype ι] (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥) :
    (∀ i, F i) ≃* G :=
  MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep
        (commuting_factors_independent F hcomm hgenerate hz),
      MonoidHom.range_eq_top.mp (by
        rw [Subgroup.noncommPiCoprod_range]
        exact hgenerate)⟩

@[simp] theorem commutingFactorsEquiv_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥)
    (i : ι) (x : F i) : commutingFactorsEquiv F hcomm hgenerate hz (Pi.mulSingle i x) = x := by
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i x

end FiniteDirectRefinement

end SimpleAmenable
end
end

end OAI
