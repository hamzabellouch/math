import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairLawAssembly
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SectorDifferenceRange
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AnchorConstants
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisAnchorFamily
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedIntervals

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GrowthGeneration
attribute [local instance] cutOrdinaryOrder

namespace growthAnchorFamily
variable (n : ℕ) (hn : 1005 ≤ n) (p : ℤ)
local notation "A" => growthAnchorFamily n hn p

theorem clipped_mem_range (i : Fin (growthAnchorLength n)) (q : ℤ)
    (hq : p ≤ q ∧ q < p+growthNewLength n) :
    clippedLabel ((A).cuts i |>.cut 0) (((A).cuts i).cut (Fin.last ((A).count i))) q ∈
      Set.range ((A).cuts i).cut := by
  rw [range,← (A).lower,← (A).upper]
  exact clippedLabel_mem _ _ _ _ _ (((A).cuts i).ordered (Fin.last ((A).count i))).1
    ((A).intervalLength (growth_lengths hn).2.2.2.1 i)
    (labels n hn p i (Fin.last ((A).count i))) hq

end growthAnchorFamily

theorem growth_edge_window {n : ℕ} (hn : 1005 ≤ n) (p : ℤ) (j : Fin (growthNewLength n-1)) :
    ∃ q : ℤ,
      (q ≤ p+(j.val:ℤ) ∧ p+(j.val:ℤ)+1 < q+growthOldLength n) ∧
      ∀ i : Fin (growthAnchorLength n+1),
        q ≤ endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) ∧
        endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) < q+growthOldLength n := by
  have hlens := growth_lengths hn
  by_cases h : p+(j.val:ℤ)+1 < p+growthOldLength n
  · refine ⟨p,⟨by omega,h⟩,?_⟩
    intro i
    have hi := growth_anchor_label hn p i
    constructor <;> omega
  · refine ⟨growthAnchorStart n p,?_,?_⟩
    · dsimp [growthAnchorStart]
      have hj := j.isLt
      have hover : growthNewLength n+201 ≤ 2*growthOldLength n := by
        simp only [growthNewLength,growthOldLength]; omega
      constructor <;> omega
    · intro i
      have hi := growth_anchor_label hn p i
      dsimp [growthAnchorStart] at hi ⊢
      constructor <;> omega

theorem axisWindowPrimitive_interval {a : ℕ} {r : CutRing} (d : Fin 2) (k : ℕ) (p : ℤ)
    (j : Fin (k-1)) :
    InitialCoverSystem.primitiveTests (a := a) (r := r) (axisWindowPrimitives d k p) j =
      coordinateInterval a d (((p+(j.val:ℤ)):CutRing)*cutTau)
        (((p+(j.val:ℤ)+1):CutRing)*cutTau) := by
  apply Subtype.ext
  change (spatialTranslate (coordinateShift d (((p+(j.val:ℤ)):CutRing)*cutTau))
    (initialTest a r (coordinateTestIndex d))).val = coordinateBetween a d _ _
  rw [initialTest_coordinate]
  unfold coordinateBetween
  have he : (((p+(j.val:ℤ)+1):CutRing)*cutTau)-(((p+(j.val:ℤ)):CutRing)*cutTau) = cutTau := by ring
  rw [he,coordinateArc_tau]
  rfl

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem primitiveFamily_range_full_all {ι : Type*} (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  classical
  let J : Finset (Fin (m+1)) := Finset.univ.erase b
  have hIJ : I ⊆ J := by intro x hx; exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hb hx,Finset.mem_univ _⟩
  have hJ : 5 ≤ J.card := by simp [J]; omega
  have hbJ : b ∉ J := Finset.notMem_erase _ _
  exact (B.primitiveFamily_range_inclusion hIJ b b hb hbJ P).trans
    (B.primitiveFamily_range_full hlarge P J hJ b hbJ)

theorem primitiveCopy_range_fullSector {ι : Type*} [Finite ι] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) (b : Fin (m+1)) (hb : b ∉ I)
    (g : B.PrimitiveFamilyLaw I b hb P) (j : ι) :
    (B.primitiveCopy I b hb (P j)).range ≤
      (B.fullGeometricSector hlarge P h (primitiveTests (a := a) (r := r) P j)).range := by
  let := alphabetPerfect I hI
  rintro x ⟨s,rfl⟩
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup I) s
  refine ⟨universalMap (subtypeAlternatingHom I) t,?_⟩
  have hh := B.fullGeometricSector_inclusion hlarge P h I hI b hb g
    (primitiveTests (a := a) (r := r) P j) (resolved_test _ j)
  rw [B.geometricSector_input I b hb P g j] at hh
  exact (DFunLike.congr_fun hh t).trans (by simp only [MonoidHom.comp_apply,ht])

end InitialCoverSystem
end GrowthGeneration

section GrowthAxisLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem growth_axis_range_prefixGroup (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
    (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ) :
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (axisWindowPrimitives d (growthNewLength n) p))).range ≤
      (growthAnchorFamily n hn p).prefixGroup B hlarge g d := by
  classical
  let A := growthAnchorFamily n hn p
  have hlens := growth_lengths hn
  rw [smallFamilyEval_range]
  apply iSup_le
  intro I
  apply iSup_le
  intro j
  cases j with
  | none =>
    change (B.initialAlphabet I.val 0).range ≤ _
    rw [B.initialAlphabet_zero]
    exact (range_comp_subset B.c _).trans
      (A.constant_range_prefixGroup B hlarge g d hlens.2.2.2.1 hlens.2.2.2.2.1)
  | some j =>
    let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
    have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
    change (B.primitiveCopy I.val b hb (axisWindowPrimitives d (growthNewLength n) p j)).range ≤ _
    obtain ⟨q,hq,ha⟩ := growth_edge_window hn p j
    let i : Fin (growthOldLength n-1) := ⟨(p+(j.val:ℤ)-q).toNat,by
      have he : ((p+(j.val:ℤ)-q).toNat:ℤ) = p+(j.val:ℤ)-q := Int.toNat_of_nonneg (by omega)
      omega⟩
    have hi : q+(i.val:ℤ) = p+(j.val:ℤ) := by
      have he : ((p+(j.val:ℤ)-q).toNat:ℤ) = p+(j.val:ℤ)-q := Int.toNat_of_nonneg (by omega)
      dsimp [i]; omega
    have he : axisWindowPrimitives d (growthOldLength n) q i =
        axisWindowPrimitives d (growthNewLength n) p j := by
      unfold axisWindowPrimitives
      congr 2
      exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) hi
    rw [← he]
    have hh := B.primitiveCopy_range_fullSector hlarge (axisWindowPrimitives d (growthOldLength n) q)
      (fun I _ b hb => B.axisFamilyLaw n g d _ hlens.1 q I b hb) I.val (by rw [I.property.2]) b hb
      (B.axisFamilyLaw n g d _ hlens.1 q I.val b hb) i
    apply hh.trans
    rw [axisWindowPrimitive_interval]
    change (B.axisSector hlarge n g d (growthOldLength n) hlens.1 q
      (coordinateInterval a d (((q+(i.val:ℤ)):CutRing)*cutTau)
        (((q+(i.val:ℤ)+1):CutRing)*cutTau))).range ≤ _
    have he0 : (((q+(i.val:ℤ)):CutRing)*cutTau) = (((p+(j.val:ℤ)):CutRing)*cutTau) := by exact_mod_cast congrArg (fun z : ℤ => (z:CutRing)*cutTau) hi
    have he1 : (((q+(i.val:ℤ)+1):CutRing)*cutTau) = (((p+(j.val:ℤ)+1):CutRing)*cutTau) := by
      congr 1; exact_mod_cast (show q+(i.val:ℤ)+1 = p+(j.val:ℤ)+1 by omega)
    rw [he0,he1]
    have hl0 : endpointLabel (((p+(j.val:ℤ)):CutRing)*cutTau) = p+(j.val:ℤ) := by
      simpa only [Int.cast_add] using endpointLabel_int_mul_tau (p+(j.val:ℤ))
    have hl1 : endpointLabel (((p+(j.val:ℤ)+1):CutRing)*cutTau) = p+(j.val:ℤ)+1 := by
      simpa only [Int.cast_add,Int.cast_one] using endpointLabel_int_mul_tau (p+(j.val:ℤ)+1)
    apply A.old_interval_range B hlarge g d hlens.2.2.2.1 (growthOldLength n) hlens.1 q _ _
    · simp only [hl0]
      omega
    · simp only [hl1]
      omega
    · exact ha
    · intro i z hz
      apply growthAnchorFamily.clipped_mem_range n hn p i
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> simp only [hl0,hl1]
      all_goals have hj := j.isLt; omega

theorem growth_axis_law_of_anchor (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
    (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ)
    (h : CentralOn (coverMap M (alternatingGenerator a r m hm))
      ((growthAnchorFamily n hn p).prefixGroup B hlarge g d))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d (growthNewLength n) p) := by
  apply CentralOn.mono h
  exact (B.primitiveFamily_range_full_all hlarge _ I b hb).trans
    (B.growth_axis_range_prefixGroup hlarge n hn g d p)

end InitialCoverSystem
end GrowthAxisLaw

end SimpleAmenable
end
end

end OAI
