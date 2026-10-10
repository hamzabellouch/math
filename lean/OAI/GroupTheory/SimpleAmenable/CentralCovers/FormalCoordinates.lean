import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairControl

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalCoordinates
variable {S Q Ω : Type*} [Group S] [Group Q] [DecidableEq Ω]

theorem coordinateFactors (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ) (ω : Ω) :
    CommutingFactors ((φ.comp (MonoidHom.mulSingle (fun _ : Ω => S) ω)).range)
      ((φ.comp (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω})).range) := by
  classical
  constructor
  · rintro x ⟨s,rfl⟩ y ⟨t,rfl⟩
    change Commute (φ (Pi.mulSingle ω s)) (φ (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} t))
    apply Commute.map _ φ
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]
  · intro x
    obtain ⟨s,rfl⟩ := hφ x
    refine ⟨φ (Pi.mulSingle ω (s ω)),⟨s ω,rfl⟩,
      φ (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} s),⟨s,rfl⟩,?_⟩
    rw [← map_mul]
    congr 1
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]

noncomputable def coordinateProjection (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ)
    (hz : Subgroup.center Q = ⊥) (ω : Ω) : Q →* Q :=
  (coordinateFactors φ hφ ω).projectLeft hz

theorem coordinateProjection_apply (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ)
    (hz : Subgroup.center Q = ⊥) (ω : Ω) (s : Ω → S) :
    coordinateProjection φ hφ hz ω (φ s) = φ (Pi.mulSingle ω (s ω)) := by
  classical
  have he : s = Pi.mulSingle ω (s ω)*assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} s := by
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]
  change (coordinateFactors φ hφ ω).projectLeft hz (φ s) = _
  conv_lhs => rw [he,map_mul]
  exact (coordinateFactors φ hφ ω).projectLeft_factors hz ⟨s ω,rfl⟩ ⟨s,rfl⟩

theorem formalMap_kill_of_actual [Finite Ω]
    (φ : (Ω → S) →* Q) (U : Set Ω)
    (hexcluded : ∀ ω, ω ∉ U → ∀ s, φ (Pi.mulSingle ω s) = 1)
    (f : Ω → S) (hf : ∀ ω ∈ U, f ω = 1) : φ f = 1 := by
  classical
  apply (Submonoid.pi_mem_of_mulSingle_mem (H := φ.ker) f)
  intro ω
  by_cases hω : ω ∈ U
  · change φ (Pi.mulSingle ω (f ω)) = 1
    rw [hf ω hω,Pi.mulSingle_one,map_one]
  · exact hexcluded ω hω (f ω)

end FormalCoordinates

section CodRestrictGeneration
variable {E G ι : Type*} [Group E] [Group G]

theorem codRestrict_iSup_top (F : ι → E →* G) (K : Subgroup G)
    (hm : ∀ i s, F i s ∈ K) (hgen : (⨆ i, (F i).range : Subgroup G) = K) :
    (⨆ i, (MonoidHom.codRestrict (F i) K (hm i)).range : Subgroup K) = ⊤ := by
  apply (Subgroup.map_injective K.subtype_injective)
  rw [Subgroup.map_iSup]
  have he (i : ι) : Subgroup.map K.subtype ((MonoidHom.codRestrict (F i) K (hm i)).range) = (F i).range := by
    rw [← MonoidHom.range_comp]
    rfl
  simp only [he]
  rw [hgen,← MonoidHom.range_eq_map,K.range_subtype]

end CodRestrictGeneration

section PairFormalLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Fintype ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairCarrierStar (j : Option ι) : TrackStar (Fin (m+1)) →*
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  (B.pairStar hlarge P h j).codRestrict _ (B.pairStar_mem hlarge P h j)

noncomputable def pairCarrierConstant : alternatingGroup (Fin (m+1)) →*
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  B.c.codRestrict _ (fun s => B.constant_range_full hlarge P ⟨s,rfl⟩)

theorem pair_formal_quotient (h20 : 20 ≤ m+1) :
    ∃ φ : ((ι → Bool) → alternatingGroup (Fin (m+1))) →*
      ((smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range ⧸
        Subgroup.center (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range),
      Function.Surjective φ ∧
      φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp (B.pairCarrierConstant hlarge P) ∧
      ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) =
        (QuotientGroup.mk' _).comp (B.pairCarrierStar hlarge P h (some i)) := by
  let : Group.IsPerfect (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
    smallFamilyEval_perfect _
  let L := fun i j => (B.pairSplit hlarge P h i j true).codRestrict _
    (B.pairSplit_mem hlarge P h i j true)
  let R := fun i j => (B.pairSplit hlarge P h i j false).codRestrict _
    (B.pairSplit_mem hlarge P h i j false)
  apply star_split_assignment (universalProjection (alternatingGroup (Fin (m+1))))
    (universalProjection_surjective _) (B.pairCarrierConstant hlarge P)
    (B.pairCarrierStar hlarge P h) rfl
    (codRestrict_iSup_top _ _ (B.pairStar_mem hlarge P h) (B.pairStar_range hlarge P h)) L R
  · intro i j s
    apply Subtype.ext
    exact B.pairStar_split hlarge P h i j s
  · intro i j k s t
    apply Subtype.ext
    exact (B.pairSplit_commute hlarge P h h20 i j k s t).eq
  · intro i
    ext s
    exact congrArg (fun f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) => f s)
      (B.pairSplit_whole_left hlarge P h i)

end InitialCoverSystem
end PairFormalLaw

section StarFormalComponents
variable {E S G ι κ Ω : Type*} [Group E] [Group S] [Group G]
    [Finite ι] [DecidableEq (ι → Bool)] [Group.IsPerfect G]
    (π : E →* S) (c : S →* G) (F : Option ι → E →* G)
    (hc : F none = c.comp π)
    (φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G))
    (hφ : Function.Surjective φ)
    (hφc : φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp c)
    (hφi : ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp π =
      (QuotientGroup.mk' _).comp (F (some i)))

include hc hφc hφi in
omit [Finite ι] [DecidableEq (ι → Bool)] [Group.IsPerfect G] in
theorem star_formal_eval : (QuotientGroup.mk' _).comp (copyFamilyEval F) =
    φ.comp (formalAssignmentEval π) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  cases i with
  | none =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily]
    rw [hc]
    exact (DFunLike.congr_fun hφc (π s)).symm
  | some i =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily]
    exact (DFunLike.congr_fun (hφi i) s).symm

noncomputable def formalCoordinateSource (σ : ι → Bool) : S →* (G ⧸ Subgroup.center G) :=
  φ.comp (MonoidHom.mulSingle (fun _ : ι → Bool => S) σ)

noncomputable def formalCoordinateMap (σ : ι → Bool) : G →* (G ⧸ Subgroup.center G) :=
  (coordinateProjection φ hφ perfect_center_quotient σ).comp (QuotientGroup.mk' _)

include hc hφc in
omit [Finite ι] in
theorem formalCoordinate_whole (σ : ι → Bool) :
    (formalCoordinateMap φ hφ σ).comp (F none) =
      (formalCoordinateSource φ σ).comp π := by
  ext s
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (F none s)) = _
  rw [hc]
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (c (π s))) = _
  have he := DFunLike.congr_fun hφc (π s)
  simp only [MonoidHom.comp_apply] at he
  rw [← he]
  simp [coordinateProjection_apply,formalCoordinateSource,sectorMask]

include hφi in
omit [Finite ι] in
theorem formalCoordinate_input (σ : ι → Bool) (i : ι) (s : E) :
    formalCoordinateMap φ hφ σ (F (some i) s) =
      if σ i then formalCoordinateSource φ σ (π s) else 1 := by
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (F (some i) s)) = _
  have he := DFunLike.congr_fun (hφi i) s
  simp only [MonoidHom.comp_apply] at he
  rw [← he]
  simp only [coordinateProjection_apply]
  cases hs : σ i <;> simp [sectorMask,hs,formalCoordinateSource]

include hc hφ hφc hφi in
omit [Finite ι] in
theorem formal_exclusion_of_subfamily [Finite κ] [Group.IsPerfect S]
    (hπ : Function.Surjective π) (v : κ → ι) (σ : ι → Bool) (pattern : Ω → κ → Bool)
    (hbad : σ ∘ v ∉ Set.range pattern)
    (hlocal : ∀ w, ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 →
      ∀ t, Commute (copyFamilyEval (fun j => F (j.map v)) w) (F none t)) :
    ∀ s, φ (Pi.mulSingle σ s) = 1 := by
  apply forbidden_factor_trivial π hπ (fun j => F (j.map v))
    (formalCoordinateMap φ hφ σ) (formalCoordinateSource φ σ) (σ ∘ v) pattern hbad
  · exact formalCoordinate_whole π c F hc φ hφ hφc σ
  · apply formal_component_of_inputs π
    · exact formalCoordinate_whole π c F hc φ hφ hφc σ
    · intro i s
      exact formalCoordinate_input π F φ hφ hφi σ (v i) s
  · exact hlocal

omit [Group.IsPerfect G] in
include hc hφc hφi in
theorem formal_centralOn_of_exclusions {H : Type*} [Group H]
    (q : G →* H) (U : Set (ι → Bool))
    (hgen : Function.Surjective (copyFamilyEval F))
    (hfaith : ∀ w, q (copyFamilyEval F w) = 1 → ∀ σ ∈ U, formalAssignmentEval π w σ = 1)
    (hkill : ∀ σ, σ ∉ U → ∀ s, φ (Pi.mulSingle σ s) = 1) :
    q.ker ≤ Subgroup.center G := by
  classical
  intro x hx
  obtain ⟨w,rfl⟩ := hgen x
  apply (QuotientGroup.eq_one_iff _).mp
  have he := DFunLike.congr_fun (star_formal_eval π c F hc φ hφc hφi) w
  rw [MonoidHom.comp_apply,MonoidHom.comp_apply] at he
  change (QuotientGroup.mk' (Subgroup.center G)) (copyFamilyEval F w) = 1
  rw [he]
  exact formalMap_kill_of_actual φ U hkill _ (hfaith w hx)

end StarFormalComponents

end SimpleAmenable
end
end

end OAI
