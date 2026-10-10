import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteSectorPartition
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SectorOffsetCoherence
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ControlledPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IndividualGridSplits
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    {ι D : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 15 < m+1)
    (Q : (i : ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : ι → polygonAlgebra a) (W : D → polygonAlgebra a)

noncomputable def gridInput (i : ι) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (Q i) (h i) (U i)

noncomputable def gridPiece (d : D) (i : ι) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (Q i) (h i) (U i ⊓ W d)

theorem gridPiece_supported
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (d : D) (i : ι) : B.AlignedSmallSupported (B.gridPiece hlarge Q h U W d i) := by
  apply B.fullGeometricSector_supported
  intro x y he
  exact and_congr (hU i x y he) (hW i d x y he)

theorem gridPiece_control (d : D) (i : ι) :
    SmallControlled B.c (B.gridPiece hlarge Q h U W d i)
      (B.fullGeometricSector hlarge (Q i) (h i) (W d)) :=
  B.fullGeometricSector_small_control hlarge _ _ _ _ inf_le_right

theorem gridInput_split
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (d : D) (i : ι) (s : TrackStar (Fin (m+1))) :
    B.gridInput hlarge Q h U i s = B.gridPiece hlarge Q h U W d i s *
      B.gridPiece hlarge Q h U (fun d => (W d)ᶜ) d i s := by
  unfold gridInput gridPiece
  rw [← B.fullGeometricSector_union hlarge _ _ (U i ⊓ W d) (U i ⊓ (W d)ᶜ)
    (fun x y he => and_congr (hU i x y he) (hW i d x y he))
    (Set.disjoint_left.mpr (by intro x hx hy; exact hy.2 hx.2))]
  congr 2
  exact (inf_sup_left _ _ _).symm.trans (by rw [sup_compl_eq_top,inf_top_eq]) |>.symm

theorem grid_complement_coherent (i₀ i : ι) (d : D)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : B.fullGeometricSector hlarge (Q i) (h i) (W d) =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)) :
    B.fullGeometricSector hlarge (Q i) (h i) (W d)ᶜ =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)ᶜ := by
  ext s
  have hi := B.fullGeometricSector_union hlarge (Q i) (h i) (W d) (W d)ᶜ (hW i d)
    (disjoint_compl_right) s
  have h₀ := B.fullGeometricSector_union hlarge (Q i₀) (h i₀) (W d) (W d)ᶜ (hW i₀ d)
    (disjoint_compl_right) s
  rw [sup_compl_eq_top] at hi
  change B.fullGeometricSector hlarge (Q i) (h i) (wholePolygon a) s = _ at hi
  rw [B.fullGeometricSector_whole,he] at hi
  rw [sup_compl_eq_top] at h₀
  change B.fullGeometricSector hlarge (Q i₀) (h i₀) (wholePolygon a) s = _ at h₀
  rw [B.fullGeometricSector_whole] at h₀
  exact mul_left_cancel (hi.symm.trans h₀)

theorem gridInputs_normalize (h20 : 20 ≤ m+1) (i₀ : ι)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector hlarge (Q i) (h i) (W d) =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)) :
    ∀ d i s, B.gridInput hlarge Q h U i s ∈
      Subgroup.normalizer ((⨆ j, (B.gridPiece hlarge Q h U W d j).range :
        Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm))) : Set _) := by
  intro d
  apply controlled_cell_normalizes _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using h20) (B.gridInput hlarge Q h U)
    (B.gridPiece hlarge Q h U W d) (B.gridPiece hlarge Q h U (fun d => (W d)ᶜ) d)
    (B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d))
    (B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)ᶜ)
  · exact B.gridPiece_supported hlarge Q h U W hU hW d
  · exact B.gridPiece_supported hlarge Q h U (fun d => (W d)ᶜ) hU
      (fun i d x y hh => not_congr (hW i d x y hh)) d
  · exact B.fullGeometricSector_supported hlarge _ _ _ (hW i₀ d)
  · intro i
    rw [← he i d]
    exact B.gridPiece_control hlarge Q h U W d i
  · intro i
    rw [← B.grid_complement_coherent hlarge Q h W i₀ i d hW (he i d)]
    exact B.gridPiece_control hlarge Q h U (fun d => (W d)ᶜ) d i
  · exact B.fullGeometricSector_commute hlarge _ _ _ _ (hW i₀ d) disjoint_compl_right
  · exact B.gridInput_split hlarge Q h U W hU hW d

theorem gridPieces_generate [Fintype D]
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val) :
    (⨆ i, (B.gridInput hlarge Q h U i).range) ≤
      ⨆ d, ⨆ i, (B.gridPiece hlarge Q h U W d i).range := by
  apply iSup_le
  intro i
  have hle := B.fullGeometricSector_partition_range hlarge (Q i) (h i) (U i)
    (fun d => U i ⊓ W d)
    (fun d x y he => and_congr (hU i x y he) (hW i d x y he))
    (fun d e hde => (hdisjoint hde).mono (fun _ hx => hx.2) (fun _ hx => hx.2))
    (fun x => by
      constructor
      · intro hx
        obtain ⟨d,hd⟩ := hcover x
        exact ⟨d,hx,hd⟩
      · rintro ⟨d,hd⟩; exact hd.1)
  exact hle.trans (iSup_mono fun d => le_iSup (fun i => (B.gridPiece hlarge Q h U W d i).range) i)

end InitialCoverSystem
end IndividualGridSplits

section SharedPrimitivePredicates

theorem spatialTranslate_integral {a : ℕ} (k : Fin 2 → ℤ) (V : polygonAlgebra a) :
    spatialTranslate ((k 0:CutRing),(k 1:CutRing)) V=V := by
  rw [spatialTranslate_reduce]
  have hz : (((k 0:CutRing).im:CutRing)*cutTau,((k 1:CutRing).im:CutRing)*cutTau) =
      (0:CutRing × CutRing) := by simp
  rw [hz]
  apply Subtype.ext
  ext p
  simp [spatialTranslate,translate_zero]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_shared_test (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (i : ι) (j : κ) (he : (P i).1=(Q j).1)
    (hp : spatialTranslate (P i).2 (initialTest a r (P i).1)=
      spatialTranslate (Q j).2 (initialTest a r (Q j).1))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun _ : Unit => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.fullGeometricSector hlarge P h V=B.fullGeometricSector hlarge Q g V := by
  let S : Unit → Fin 5 × (CutRing × CutRing) := fun _ => P i
  let T : Unit → Fin 5 × (CutRing × CutRing) := fun _ => Q j
  have hS := fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb P (h I hI b hb) (fun _ : Unit => i)
  have hT := fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb Q (g I hI b hb) (fun _ : Unit => j)
  have hV' : ResolvedBy (fun _ : Unit => (primitiveTests (a := a) (r := r) Q j).val) V.val := by
    intro x y hxy
    apply hV x y
    intro z
    change x ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val ↔
      y ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val
    rw [hp]
    exact hxy ()
  rw [← B.fullGeometricSector_subfamily hlarge P S (fun _ => i) rfl h hS V hV,
    ← B.fullGeometricSector_subfamily hlarge Q T (fun _ => j) rfl g hT V hV']
  exact B.fullGeometricSector_congr_offsets hlarge S T (fun _ => he) (fun _ => hp) hS hT V hV

theorem tangentSign_integral (hlarge : 15 < m+1)
    (n : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws n q u)
    (d : Fin 2) (k : Fin 2 → ℤ) (positive : Bool) :
    B.tangentSign hlarge n q u h d ((k 0:CutRing),(k 1:CutRing)) positive=
      B.tangentSign hlarge n q u h d 0 positive := by
  unfold tangentSign
  have hp (V : polygonAlgebra a) : spatialTranslate ((k 0:CutRing),(k 1:CutRing)) V=
      spatialTranslate 0 V := by
    rw [spatialTranslate_integral]
    apply Subtype.ext
    ext p
    simp [spatialTranslate,translate_zero]
  rw [hp]
  apply B.fullGeometricSector_shared_test hlarge _ _ (Sum.inl (0:Fin 2)) (Sum.inl (0:Fin 2))
  · rfl
  · simp only [translatedTemplate,tangentChartTemplate,ite_true,add_zero]
    exact hp _
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate (((k 0:CutRing),(k 1:CutRing))+0)
        (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate (((k 0:CutRing),(k 1:CutRing))+0)
        (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope,hp] at hh
    cases positive with
    | false => exact not_congr hh
    | true => exact hh

end InitialCoverSystem
end SharedPrimitivePredicates

end SimpleAmenable
end
end

end OAI
