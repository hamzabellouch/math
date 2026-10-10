import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalCoordinates

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualStarProjection
variable {a m : ℕ} {ι : Type*} [Finite ι]

noncomputable def formalPolygonTable (U : ι → polygonAlgebra a) :
    ((ι → Bool) → alternatingGroup (Fin (m+1))) →* polygonAlternatingGroup a (m+1) :=
  (actualPolygonTableHom U).comp (assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val))

theorem formalPolygonTable_whole (U : ι → polygonAlgebra a) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask Set.univ s) = conditionalAlternatingHom (wholePolygon a) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask Set.univ s) = sectorMask Set.univ s := by
    ext ω; simp [assignmentPullback,sectorMask]
  rw [he]
  exact actualPolygonTableHom_whole U s

theorem formalPolygonTable_test (U : ι → polygonAlgebra a) (i : ι) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask {σ | σ i = true} s) = conditionalAlternatingHom (U i) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask {σ | σ i = true} s) = polygonTableInput U i s := by rfl
  rw [he]
  exact actualPolygonTableHom_input U i s

theorem formalPolygonTable_eq_one (U : ι → polygonAlgebra a)
    (f : (ι → Bool) → alternatingGroup (Fin (m+1))) (h : formalPolygonTable U f = 1)
    (σ : ι → Bool) (hσ : σ ∈ Set.range (polygonAssignment U)) : f σ = 1 := by
  have he := actualPolygonTableHom_injective U (h.trans (map_one _).symm)
  exact congrFun he ⟨σ,hσ⟩

variable {E H : Type*} [Group E] [Group H]

theorem actualStar_eval_projection (π : E →* alternatingGroup (Fin (m+1)))
    (U : ι → polygonAlgebra a) (F : Option ι → E →* H)
    (q : H →* polygonAlternatingGroup a (m+1))
    (hq : ∀ j, q.comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp π) :
    q.comp (copyFamilyEval F) = (formalPolygonTable U).comp (formalAssignmentEval π) := by
  apply FreeGroup.ext_hom
  rintro ⟨j,s⟩
  simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
    FreeGroup.map.of,assignmentEval]
  have he := DFunLike.congr_fun (hq j) s
  simp only [MonoidHom.comp_apply] at he
  rw [he]
  cases j with
  | none => exact (formalPolygonTable_whole U (π s)).symm
  | some i => exact (formalPolygonTable_test U i (π s)).symm

end ActualStarProjection

section PairProjection
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] in
theorem pairStar_projection (j : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.pairStar hlarge P h j) =
      (conditionalAlternatingHom (primitiveFamilyTests (a := a) (r := r) P j)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) := by
  cases j with
  | none =>
    change (coverMap _ _).comp (B.c.comp _) = _
    rw [← MonoidHom.comp_assoc,B.c_projection]
    rfl
  | some i =>
    exact B.fullGeometricSector_projection hlarge _ _ _ (primitivePair_left_resolved P i i)

omit [Finite ι] in

theorem pairStar_subfamily_mem (v : κ → ι)
    (hp : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (j : Option κ) (s : TrackStar (Fin (m+1))) :
    B.pairStar hlarge P h (j.map v) s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range := by
  cases j with
  | none => exact B.constant_range_full hlarge (P ∘ v) ⟨_,rfl⟩
  | some j =>
    change B.fullGeometricSector hlarge (primitivePair P (v j) (v j)) (h (v j) (v j))
      (primitiveTests (a := a) (r := r) (primitivePair P (v j) (v j)) false) s ∈ _
    rw [B.fullGeometricSector_shared_primitive hlarge (primitivePair P (v j) (v j)) (P ∘ v)
      false j rfl _ hp _ (resolved_test _ ())]
    exact B.fullGeometricSector_mem hlarge _ hp _ s

end InitialCoverSystem
end PairProjection

section PairExclusionLocal
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] in
theorem pairStar_subfamily_local (v : κ → ι)
    (hp : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (w : FreeGroup (Option κ × TrackStar (Fin (m+1))))
    (hw : ((assignmentPullback (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)))).comp
      (formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))))) w = 1)
    (s : TrackStar (Fin (m+1))) :
    Commute (copyFamilyEval (fun j => B.pairStar hlarge P h (j.map v)) w)
      (B.pairStar hlarge P h none s) := by
  let U := primitiveTests (a := a) (r := r) (P ∘ v)
  let F := fun j : Option κ => B.pairStar hlarge P h (j.map v)
  have hproj j : (coverMap M (alternatingGenerator a r m hm)).comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) := by
    rw [show F j = B.pairStar hlarge P h (j.map v) from rfl,B.pairStar_projection]
    cases j <;> rfl
  have he := DFunLike.congr_fun (actualStar_eval_projection
    (universalProjection (alternatingGroup (Fin (m+1)))) U F _ hproj) w
  simp only [MonoidHom.comp_apply] at he
  have hz : (coverMap M (alternatingGenerator a r m hm)) (copyFamilyEval F w) = 1 := by
    rw [he]
    change actualPolygonTableHom U _ = 1
    have hz : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
        (formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))) w) = 1 := by
      funext ω
      obtain ⟨p,hp⟩ := ω.property
      have he := congrFun hw p
      change formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))) w
        (polygonAssignment U p) = 1 at he
      simpa only [assignmentPullback,MonoidHom.coe_mk,OneHom.coe_mk,Function.comp_apply,hp,Pi.one_apply] using he
    rw [hz,map_one]
  have hm : (copyFamilyEval F).range ≤ (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range := by
    rw [copyFamilyEval_range]
    apply iSup_le
    rintro j x ⟨t,rfl⟩
    exact B.pairStar_subfamily_mem hlarge P h v hp j t
  exact (centralOn_iff _ _).mp (B.fullPrimitiveFamily_central hlarge (P ∘ v) hp)
    _ (hm ⟨w,rfl⟩) hz _ (B.constant_range_full hlarge (P ∘ v) ⟨_,rfl⟩)

end InitialCoverSystem
end PairExclusionLocal

section PairActualLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ D : Type*} [Fintype ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

include h in

theorem pair_actual_central (h20 : 20 ≤ m+1) (v : D → κ → ι)
    (hp : ∀ d I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v d))
    (hexclude : ∀ σ : ι → Bool,
      σ ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) →
      ∃ d, σ ∘ v d ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d)))) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  classical
  let K := (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
  let : Group.IsPerfect K := smallFamilyEval_perfect _
  let π := universalProjection (alternatingGroup (Fin (m+1)))
  let F := B.pairCarrierStar hlarge P h
  let c := B.pairCarrierConstant hlarge P
  let q := (coverMap M (alternatingGenerator a r m hm)).comp K.subtype
  let U := primitiveTests (a := a) (r := r) P
  obtain ⟨φ,hφ,hφc,hφi⟩ := B.pair_formal_quotient hlarge P h h20
  have hF : F none = c.comp π := rfl
  have hgen : Function.Surjective (copyFamilyEval F) := by
    apply MonoidHom.range_eq_top.mp
    rw [copyFamilyEval_range]
    exact codRestrict_iSup_top _ _ (B.pairStar_mem hlarge P h) (B.pairStar_range hlarge P h)
  have hproj j : q.comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp π := by
    change (coverMap _ _).comp (B.pairStar hlarge P h j) = _
    rw [B.pairStar_projection]
    cases j <;> rfl
  have heval := actualStar_eval_projection π U F q hproj
  apply formal_centralOn_of_exclusions π c F hF φ hφc hφi q
    (Set.range (polygonAssignment U)) hgen
  · intro w hw σ hσ
    have he := DFunLike.congr_fun heval w
    simp only [MonoidHom.comp_apply] at he
    exact formalPolygonTable_eq_one U _ (he.symm.trans hw) σ hσ
  · intro σ hσ
    obtain ⟨d,hd⟩ := hexclude σ hσ
    apply formal_exclusion_of_subfamily π c F hF φ hφ hφc hφi
      (universalProjection_surjective _) (v d) σ
      (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d))) hd
    intro w hw t
    apply Subtype.ext
    have he := DFunLike.congr_fun (copyFamilyEval_comp (fun j => F (j.map (v d))) K.subtype) w
    change copyFamilyEval (fun j => B.pairStar hlarge P h (j.map (v d))) w =
      (copyFamilyEval (fun j => F (j.map (v d))) w).val at he
    change (copyFamilyEval (fun j => F (j.map (v d))) w).val * B.pairStar hlarge P h none t =
      B.pairStar hlarge P h none t * (copyFamilyEval (fun j => F (j.map (v d))) w).val
    rw [← he]
    exact (B.pairStar_subfamily_local hlarge P h (v d) (hp d) w hw t).eq

include hlarge h in

theorem pair_actual_law (h20 : 20 ≤ m+1) (v : D → κ → ι)
    (hp : ∀ d I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v d))
    (hexclude : ∀ σ : ι → Bool,
      σ ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) →
      ∃ d, σ ∘ v d ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d))))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) : B.PrimitiveFamilyLaw I b hb P :=
  (B.pair_actual_central hlarge P h h20 v hp hexclude).mono
    (B.primitiveFamily_range_full_all hlarge P I b hb)

end InitialCoverSystem
end PairActualLaw

end SimpleAmenable
end
end

end OAI
