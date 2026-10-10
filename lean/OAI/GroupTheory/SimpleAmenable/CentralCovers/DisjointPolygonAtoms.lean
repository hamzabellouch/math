import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisCutSequences
import OAI.GroupTheory.SimpleAmenable.Configurations.ConditionalIntervalDifference

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DisjointPolygonAtoms
variable {a m : ℕ} {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
theorem polygonTableInput_disjoint (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) :
    Pairwise fun i j => ∀ s t : alternatingGroup (Fin m),
      Commute (polygonTableInput U i s) (polygonTableInput U j t) := by
  intro i j hij s t
  apply sectorMask_commute
  apply Set.disjoint_left.mpr
  rintro ⟨ω,p,rfl⟩ hi hj
  have hi' : p ∈ (U i).val := by simpa [polygonAssignment] using hi
  have hj' : p ∈ (U j).val := by simpa [polygonAssignment] using hj
  exact Set.disjoint_left.mp (hd hij) hi' hj'

noncomputable def polygonDisjointTable (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) :
    (Ω → alternatingGroup (Fin m)) →* polygonAlternatingGroup a m :=
  (actualPolygonTableHom U).comp (MonoidHom.noncommPiCoprod
    (fun i => polygonTableInput U i) (polygonTableInput_disjoint U hd))

@[simp] theorem polygonDisjointTable_single [DecidableEq Ω] (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) (i : Ω) (s : alternatingGroup (Fin m)) :
    polygonDisjointTable U hd (Pi.mulSingle i s) = conditionalAlternatingHom (U i) s := by
  simp only [polygonDisjointTable,MonoidHom.comp_apply,MonoidHom.noncommPiCoprod_mulSingle,
    actualPolygonTableHom_input]

theorem polygonDisjointTable_mask (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val) (i : Ω) :
    (polygonDisjointTable (m := m) U hd).comp (sectorMask {i}) = conditionalAlternatingHom (U i) := by
  classical
  ext s : 1
  have he : sectorMask {i} s = Pi.mulSingle i s := by
    ext j
    by_cases hh : j=i <;> simp [sectorMask,hh]
  simp only [MonoidHom.comp_apply,he,polygonDisjointTable_single]

theorem polygonDisjointTable_injective (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val)
    (hne : ∀ i, (U i).val.Nonempty) : Function.Injective (polygonDisjointTable (m := m) U hd) := by
  classical
  let F := MonoidHom.noncommPiCoprod (fun i => polygonTableInput (m := m) U i)
    (polygonTableInput_disjoint U hd)
  intro s t he
  have hs : F s = F t := actualPolygonTableHom_injective U he
  funext i
  obtain ⟨p,hp⟩ := hne i
  let ω : Set.range (polygonAssignment U) := ⟨polygonAssignment U p,⟨p,rfl⟩⟩
  have hω (j : Ω) : ω.val j = true ↔ j=i := by
    change decide (p ∈ (U j).val) = true ↔ j=i
    simp only [decide_eq_true_eq]
    constructor
    · intro hj
      by_contra hh
      exact Set.disjoint_left.mp (hd hh) hj hp
    · rintro rfl; exact hp
  have hEval : (Pi.evalMonoidHom (fun _ : Set.range (polygonAssignment U) => alternatingGroup (Fin m)) ω).comp F =
      Pi.evalMonoidHom (fun _ : Ω => alternatingGroup (Fin m)) i := by
    apply MonoidHom.pi_ext
    intro j x
    change F (Pi.mulSingle j x) ω = (Pi.mulSingle j x : Ω → alternatingGroup (Fin m)) i
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    by_cases hh : j=i
    · subst j
      simp [polygonTableInput,sectorMask,hω]
    · have hh' : ¬ω.val j = true := by simpa only [hω j] using hh
      simp [polygonTableInput,sectorMask,hh',Ne.symm hh]
  have hx := congrArg (fun z => z ω) hs
  have hsEval := DFunLike.congr_fun hEval s
  have htEval := DFunLike.congr_fun hEval t
  change F s ω = s i at hsEval
  change F t ω = t i at htEval
  rwa [hsEval,htEval] at hx

theorem centralOn_disjoint_polygon_atoms {H : Type*} [Group H]
    (q : H →* polygonAlternatingGroup a m) (U : Ω → polygonAlgebra a)
    (hd : Pairwise fun i j => Disjoint (U i).val (U j).val)
    (hne : ∀ i, (U i).val.Nonempty)
    (f : Ω → UniversalExtension (alternatingGroup (Fin m)) →* H)
    (hc : Pairwise fun i j => ∀ s t, Commute (f i s) (f j t))
    (hp : ∀ i, q.comp (f i) = (conditionalAlternatingHom (U i)).comp
      (universalProjection (alternatingGroup (Fin m)))) :
    CentralOn q (⨆ i, (f i).range) := by
  apply centralOn_of_star_atoms q (polygonDisjointTable U hd)
    (polygonDisjointTable_injective U hd hne) f hc
  intro i
  rw [polygonDisjointTable_mask]
  exact hp i

end DisjointPolygonAtoms

section AxisCutAtoms
namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)
    {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)
    (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1)
    (hc : ∀ i j : ℕ, i ≤ j → ∀ x y,
      Commute (D.prefixCopy B hlarge g d i x) (D.suffix B hlarge g d j y))

noncomputable def atomCopy (i : Fin K) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  cutDifference (D.anchorCopy B hlarge g d) (D.prefixCopy B hlarge g d)
    (D.suffix B hlarge g d) (D.prefix_suffix B hlarge g d hlen) hc i.val

noncomputable def atomPolygon (i : Fin K) : polygonAlgebra a :=
  coordinateInterval a d (D.cut i.castSucc) (D.cut i.succ)

include hlen in
theorem atomPolygon_nonempty (i : Fin K) : (D.atomPolygon d i : polygonAlgebra a).val.Nonempty := by
  apply coordinateInterval_nonempty
  · exact D.strictMono (Fin.castSucc_lt_succ (i := i))
  · have h₁ := (D.ordered i.castSucc).1
    have h₂ := (D.ordered i.succ).2
    linarith

include hlen in
theorem atomPolygon_disjoint : Pairwise fun i j : Fin K =>
    Disjoint (D.atomPolygon d i : polygonAlgebra a).val (D.atomPolygon d j).val := by
  intro i j hij
  have one (i j : Fin K) (hij : i < j) :
      Disjoint (D.atomPolygon d i : polygonAlgebra a).val (D.atomPolygon d j).val := by
    have hgap : i.succ ≤ j.castSucc := by simpa only [Fin.le_def,Fin.val_succ,Fin.val_castSucc] using (show i.val+1 ≤ j.val by omega)
    apply coordinateInterval_disjoint
    · exact (D.strictMono (Fin.castSucc_lt_succ (i := i))).le
    · exact D.strictMono.monotone hgap
    · exact (D.strictMono (Fin.castSucc_lt_succ (i := j))).le
    · have h₁ := (D.ordered i.castSucc).1
      have h₂ := (D.ordered j.succ).2
      linarith
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact one i j hh
  · exact (one j i hh).symm

theorem atomCopy_projection (i : Fin K) :
    (coverMap M (alternatingGenerator a r m hm)).comp (D.atomCopy B hlarge g d hlen hc i) =
      (conditionalAlternatingHom (D.atomPolygon d i)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) := by
  ext x : 1
  change coverMap M (alternatingGenerator a r m hm)
    ((D.prefixCopy B hlarge g d i.val x)⁻¹*D.prefixCopy B hlarge g d (i.val+1) x) = _
  rw [map_mul,map_inv]
  have h₁ := DFunLike.congr_fun (D.prefix_projection B hlarge g d i.val) x
  have h₂ := DFunLike.congr_fun (D.prefix_projection B hlarge g d (i.val+1)) x
  simp only [MonoidHom.comp_apply] at h₁ h₂
  rw [h₁,h₂]
  have hi : D.index i.val = i.castSucc := D.index_fin i.castSucc
  have hi' : D.index (i.val+1) = i.succ := D.index_fin i.succ
  rw [hi,hi']
  apply conditionalAlternatingHom_interval_difference
  · exact (D.ordered i.castSucc).1
  · exact (D.strictMono (Fin.castSucc_lt_succ (i := i))).le
  · have hh := (D.ordered i.succ).2
    linarith

theorem atomCopy_commute : Pairwise fun i j : Fin K => ∀ x y,
    Commute (D.atomCopy B hlarge g d hlen hc i x) (D.atomCopy B hlarge g d hlen hc j y) := by
  intro i j hij x y
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact cutDifference_pairwise _ _ _ _ _ i.val j.val hh x y
  · exact (cutDifference_pairwise _ _ _ _ _ j.val i.val hh y x).symm

theorem atomCopy_supported (i : Fin K) :
    B.AlignedSmallSupported (D.atomCopy B hlarge g d hlen hc i) :=
  cutDifference_small_supported (sourceAlignedGroup a r m hm M B.t) _ _ _ _ _
    (D.prefix_small_supported B hlarge g d) i.val

theorem atomCopy_controlled (i : Fin K) :
    SmallControlled B.c (D.atomCopy B hlarge g d hlen hc i) (D.anchorCopy B hlarge g d) :=
  cutDifference_small_controlled B.c _ _ _ _ _
    (D.prefix_small_controlled B hlarge g d hlen) i.val

include hlen hc in

theorem cuts_central : CentralOn (coverMap M (alternatingGenerator a r m hm))
    (⨆ i : Fin (K+1), (D.prefixCopy B hlarge g d i.val).range) := by
  have hcentral := centralOn_disjoint_polygon_atoms
    (coverMap M (alternatingGenerator a r m hm)) (D.atomPolygon d)
    (D.atomPolygon_disjoint d hlen) (D.atomPolygon_nonempty d hlen)
    (D.atomCopy B hlarge g d hlen hc) (D.atomCopy_commute B hlarge g d hlen hc)
    (D.atomCopy_projection B hlarge g d hlen hc)
  apply hcentral.mono
  apply iSup_le
  intro i
  exact prefix_range_le_differences _ _ _ _ hc (D.prefix_zero B hlarge g d) K i.val (by omega)

end AxisCutSequence
end AxisCutAtoms

end SimpleAmenable
end
end

end OAI
