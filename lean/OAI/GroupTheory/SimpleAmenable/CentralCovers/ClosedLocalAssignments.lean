import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalGridPieces
import OAI.GroupTheory.SimpleAmenable.CentralCovers.LocalArrangementAssignments
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClosedSquareGerms
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateActualRelators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClosedLocalAssignments
variable {a : ℕ} {ι κ : Type*}

theorem localCutFamily_assignment_realized_closed [Finite ι]
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (y : GenericSquare a) (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧
      polygonAssignment (fun i => cutPolygon a (j i) (c i)) p=
        polygonAssignment (localCutFamily j c z) y := by
  classical
  let σ := polygonAssignment (localCutFamily (a := a) j c z) y
  have hactive : ∀ i, cutForm a (j i) z=ordinary (c i) →
      if σ i then cutForm a (j i) y.val<ordinary (c i)
      else ordinary (c i)<cutForm a (j i) y.val := by
    intro i hi
    have hσ : σ i=decide (cutForm a (j i) y.val<ordinary (c i)) := by
      simp [σ,polygonAssignment,localCutFamily,hi,cutPolygon,halfPlane]
    rw [hσ]
    split_ifs with h
    · exact of_decide_eq_true h
    · have hn := of_decide_eq_false (Bool.eq_false_iff.mpr h)
      exact lt_of_le_of_ne (le_of_not_gt hn) (y.property.2.2 (j i) (c i)).symm
  have hinactive : ∀ i, cutForm a (j i) z≠ordinary (c i) →
      if σ i then cutForm a (j i) z<ordinary (c i)
      else ordinary (c i)<cutForm a (j i) z := by
    intro i hi
    by_cases hlt : cutForm a (j i) z<ordinary (c i)
    · simp [σ,polygonAssignment,localCutFamily,hi,hlt]
    · simp only [σ,polygonAssignment,localCutFamily,ite_eq_right hi,ite_eq_right hlt]
      simpa using lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
  obtain ⟨p,hp,hcell⟩ := finite_arrangement_germ_square a j (fun i => ordinary (c i))
    z y σ hz₁ hz₂ hactive hinactive N hN hz
  refine ⟨p,hp,?_⟩
  funext i
  change decide (cutForm a (j i) p.val<ordinary (c i))=σ i
  have hi := hcell i
  cases he : σ i
  · simp only [he,Bool.false_eq_true,↓reduceIte] at hi
    exact decide_eq_false (not_lt_of_gt hi)
  · simp only [he,↓reduceIte] at hi
    exact decide_eq_true hi

theorem localCutFamily_range_subset_closed [Finite ι]
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1) :
    Set.range (polygonAssignment (localCutFamily (a := a) j c z)) ⊆
      Set.range (polygonAssignment (fun i => cutPolygon a (j i) (c i))) := by
  rintro σ ⟨y,rfl⟩
  obtain ⟨p,_,hp⟩ := localCutFamily_assignment_realized_closed j c z hz₁ hz₂ y Set.univ isOpen_univ (Set.mem_univ z)
  exact ⟨p,hp⟩

theorem localPolygonFamily_assignment_realized_closed [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val)
    (y : GenericSquare a) (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧
      polygonAssignment R p=polygonAssignment (localPolygonFamily j c z R) y := by
  obtain ⟨p,hp,he⟩ := localCutFamily_assignment_realized_closed j c z hz₁ hz₂ y N hN hz
  refine ⟨p,hp,?_⟩
  funext i
  apply decide_eq_decide.mpr
  change (p ∈ (R i).val) ↔ polygonAssignment (localCutFamily j c z) y ∈
    polygonFormalMask (fun k => cutPolygon a (j k) (c k)) (R i)
  rw [← he]
  exact (polygonFormalMask_mem _ (R i) (hR i) p).symm

theorem localPolygonFamily_range_subset_closed [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val) :
    Set.range (polygonAssignment (localPolygonFamily j c z R)) ⊆ Set.range (polygonAssignment R) := by
  rintro σ ⟨y,rfl⟩
  obtain ⟨p,_,hp⟩ := localPolygonFamily_assignment_realized_closed j c z hz₁ hz₂ R hR y
    Set.univ isOpen_univ (Set.mem_univ z)
  exact ⟨p,hp⟩

end ClosedLocalAssignments

section IndependentActualPatching
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem independent_actual_patching (hlarge : 25 ≤ m+1)
    (F : (i : Option ι) → Option (κ i) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (T : ∀ i, FormalStarTable (F i)) (U : (i : Option ι) → Set (κ i → Bool))
    (C : (i : Option ι) → D → Set (κ i → Bool))
    (hF : ∀ i j, B.AlignedSmallSupported (F i j))
    (hc : ∀ i, F i none=B.c.comp (universalProjection _))
    (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
    (hcover : ∀ i σ, ∃ d, σ ∈ C i d)
    (j k : D → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hj : ∀ i d, (T i).sector (C i d)=j d)
    (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
    (hjs : ∀ d, B.AlignedSmallSupported (j d))
    (hcomm : ∀ d s t, Commute (j d s) (k d t))
    (hzero : formalGridInput F T U none=B.c.comp (universalProjection _))
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (formalGridInput F T U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (R : ι → polygonAlgebra a)
    (L : ∀ d, B.LocalPatchTemplate (by omega)
      (formalGridInput F T U) (formalGridPiece F T U C d))
    (hreal : ∀ d x, x ∈ (L d).margin.val →
      polygonAssignment (L d).predicates x ∈ Set.range (polygonAssignment R)) :
    HasCentralLaw (smallFamilyModel (actualTestMask R)) (smallFamilyEval f).rangeRestrict := by
  classical
  have hpieces d i : B.AlignedSmallSupported (formalGridPiece F T U C d i) :=
    formalGridPiece_supported F T U C _ hF d i
  apply supported_assignment_patching (actualTestMask R) ?_
    (formalGridInput F T U) f hspec
    (fun d => ⨆ i, (formalGridPiece F T U C d i).range) ?_ ?_
    (fun d i => B.fullGeometricSector (by omega) (L d).tests (L d).lawful
      (marginFamily (L d).predicates (L d).margin i)) ?_ ?_
    (by simp only [Fintype.card_fin]; omega)
  · intro σ τ h
    apply Subtype.ext
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  · rw [copyFamilyEval_range]
    exact formalGridPieces_generate F T U C hd hcover
  · exact formalGridInputs_normalize F T U C _ B.c
      (by simp only [Fintype.card_fin]; omega) B.constant_aligned B.disjoint_aligned
      hF hc j k hj hk hjs hcomm
  · intro d I i s
    apply inner_action_iSup
    intro e
    exact (L d).masked_actions (by omega) hzero (hpieces d) i I s e
  · intro d S hS w hw hrel
    have hh : (⨆ i, (formalGridPiece F T U C d i).range) ≤
        Subgroup.centralizer ({copyFamilyEval
          (fun i => B.fullGeometricSector (by omega) (L d).tests (L d).lawful
            (marginFamily (L d).predicates (L d).margin i))
          (smallFamilyStarWord w)} : Set _) := by
      apply iSup_le
      intro i x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (B.actual_template_actual_word_controls hlarge (L d).tests (L d).lawful
        (L d).predicates (L d).margin (L d).predicates_resolved (L d).margin_resolved
        _ (hpieces d i) ((L d).controlled i) S hS w hw R (hreal d) hrel x hx).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hh hx)).symm

end InitialCoverSystem
end IndependentActualPatching

end SimpleAmenable
end
end

end OAI
