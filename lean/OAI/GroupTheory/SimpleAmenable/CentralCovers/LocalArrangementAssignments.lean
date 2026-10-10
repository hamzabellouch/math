import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ResolvedBoolean
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalArrangementAssignments
variable {a : ℕ} {ι : Type*}

noncomputable def cutPolygon (a : ℕ) (j : Fin 4) (c : CutRing) : polygonAlgebra a :=
  ⟨halfPlane a j c,halfPlane_mem a j c⟩

noncomputable def localCutFamily (j : ι → Fin 4) (c : ι → CutRing)
    (z : ℝ × ℝ) (i : ι) : polygonAlgebra a := by
  classical
  exact if cutForm a (j i) z=ordinary (c i) then cutPolygon a (j i) (c i)
    else if cutForm a (j i) z<ordinary (c i) then ⊤ else ⊥

theorem localCutFamily_assignment_realized [Finite ι]
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Ioo (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Ioo (0:ℝ) 1)
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
  let V : Set (ℝ × ℝ) := N ∩ (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1)
  have hV : IsOpen V := hN.inter (isOpen_Ioo.prod isOpen_Ioo)
  obtain ⟨p,hp,hcell,hgeneric⟩ := finite_arrangement_germ a j (fun i => ordinary (c i))
    z y.val σ hactive hinactive V hV ⟨hz,hz₁,hz₂⟩
  let p' : GenericSquare a := ⟨p,⟨hp.2.1.1.le,hp.2.1.2⟩,⟨hp.2.2.1.le,hp.2.2.2⟩,hgeneric⟩
  refine ⟨p',hp.1,?_⟩
  funext i
  change decide (cutForm a (j i) p<ordinary (c i))=σ i
  have hi := hcell i
  cases he : σ i
  · simp only [he,Bool.false_eq_true,↓reduceIte] at hi
    exact decide_eq_false (not_lt_of_gt hi)
  · simp only [he,↓reduceIte] at hi
    exact decide_eq_true hi

theorem localCutFamily_range_subset [Finite ι]
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Ioo (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Ioo (0:ℝ) 1) :
    Set.range (polygonAssignment (localCutFamily (a := a) j c z)) ⊆
      Set.range (polygonAssignment (fun i => cutPolygon a (j i) (c i))) := by
  rintro σ ⟨y,rfl⟩
  obtain ⟨p,_,hp⟩ := localCutFamily_assignment_realized j c z hz₁ hz₂ y Set.univ isOpen_univ (Set.mem_univ z)
  exact ⟨p,hp⟩

end LocalArrangementAssignments

section LocalBooleanAssignments
variable {a : ℕ} {ι κ : Type*}

noncomputable def polygonBooleanPullback [Finite κ] (U : κ → polygonAlgebra a)
    (S : Set (κ → Bool)) : polygonAlgebra a := by
  refine ⟨{p | polygonAssignment U p ∈ S},?_⟩
  have he : {p | polygonAssignment U p ∈ S}=
      ⋃ σ : S, {p | polygonAssignment U p=σ.val} := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h; exact ⟨⟨_,h⟩,rfl⟩
    · rintro ⟨σ,hσ⟩; exact hσ ▸ σ.property
  rw [he]
  exact BooleanSubalgebra.iSup_mem fun σ => polygonAssignment_fiber_mem U σ.val

noncomputable def polygonFormalMask (U : κ → polygonAlgebra a)
    (V : polygonAlgebra a) : Set (κ → Bool) :=
  {σ | ∃ p, polygonAssignment U p=σ ∧ p ∈ V.val}

theorem polygonFormalMask_mem (U : κ → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) (p : GenericSquare a) :
    polygonAssignment U p ∈ polygonFormalMask U V ↔ p ∈ V.val := by
  constructor
  · rintro ⟨q,hq,hqV⟩
    exact (hV q p ((polygonAssignment_eq_iff U q p).mp hq)).mp hqV
  · intro hp; exact ⟨p,rfl,hp⟩

theorem polygonBooleanPullback_formalMask [Finite κ]
    (U : κ → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) :
    polygonBooleanPullback U (polygonFormalMask U V)=V := by
  apply Subtype.ext
  ext p
  exact polygonFormalMask_mem U V hV p

noncomputable def localPolygonFamily [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (R : ι → polygonAlgebra a) (i : ι) : polygonAlgebra a :=
  polygonBooleanPullback (localCutFamily j c z)
    (polygonFormalMask (fun k => cutPolygon a (j k) (c k)) (R i))

theorem localPolygonFamily_assignment_realized [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Ioo (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Ioo (0:ℝ) 1)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val)
    (y : GenericSquare a) (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧
      polygonAssignment R p=polygonAssignment (localPolygonFamily j c z R) y := by
  obtain ⟨p,hp,he⟩ := localCutFamily_assignment_realized j c z hz₁ hz₂ y N hN hz
  refine ⟨p,hp,?_⟩
  funext i
  apply decide_eq_decide.mpr
  change (p ∈ (R i).val) ↔ polygonAssignment (localCutFamily j c z) y ∈
    polygonFormalMask (fun k => cutPolygon a (j k) (c k)) (R i)
  rw [← he]
  exact (polygonFormalMask_mem _ (R i) (hR i) p).symm

theorem localPolygonFamily_range_subset [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Ioo (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Ioo (0:ℝ) 1)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val) :
    Set.range (polygonAssignment (localPolygonFamily j c z R)) ⊆ Set.range (polygonAssignment R) := by
  rintro σ ⟨y,rfl⟩
  obtain ⟨p,_,hp⟩ := localPolygonFamily_assignment_realized j c z hz₁ hz₂ R hR y
    Set.univ isOpen_univ (Set.mem_univ z)
  exact ⟨p,hp⟩

theorem localCutFamily_locally_eq [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ p : GenericSquare a, p.val ∈ N →
        polygonAssignment (localCutFamily j c z) p=
          polygonAssignment (fun k => cutPolygon a (j k) (c k)) p := by
  classical
  let N : Set (ℝ × ℝ) := ⋂ k,
    if cutForm a (j k) z=ordinary (c k) then Set.univ
    else if cutForm a (j k) z<ordinary (c k)
    then {p | cutForm a (j k) p<ordinary (c k)}
    else {p | ordinary (c k)<cutForm a (j k) p}
  refine ⟨N,?_,?_,?_⟩
  · apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt (cutForm_continuous a (j k)) continuous_const
    · exact isOpen_lt continuous_const (cutForm_continuous a (j k))
  · apply Set.mem_iInter.mpr
    intro k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · rw [ite_eq_left he]; trivial
    · rw [ite_eq_right he]
      by_cases hl : cutForm a (j k) z<ordinary (c k)
      · rw [ite_eq_left hl]; exact hl
      · rw [ite_eq_right hl]; exact lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
  · intro p hp
    funext k
    have hk := Set.mem_iInter.mp hp k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · simp [polygonAssignment,localCutFamily,he]
    · by_cases hl : cutForm a (j k) z<ordinary (c k)
      · simp only [ite_eq_right he,ite_eq_left hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,hk]
      · simp only [ite_eq_right he,ite_eq_right hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,not_lt_of_gt hk]

theorem localPolygonFamily_locally_eq [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ p : GenericSquare a, p.val ∈ N → ∀ i,
        p ∈ (localPolygonFamily j c z R i).val ↔ p ∈ (R i).val := by
  obtain ⟨N,hN,hz,h⟩ := localCutFamily_locally_eq (a := a) j c z
  refine ⟨N,hN,hz,fun p hp i => ?_⟩
  change polygonAssignment (localCutFamily j c z) p ∈ polygonFormalMask _ (R i) ↔ _
  rw [h p hp]
  exact polygonFormalMask_mem _ (R i) (hR i) p

end LocalBooleanAssignments

end SimpleAmenable
end
end

end OAI
