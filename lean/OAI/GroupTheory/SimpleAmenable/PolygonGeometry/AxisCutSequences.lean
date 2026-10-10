import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AxisSplitting
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SeparatedAxisSectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AxisCutSequences

structure AxisCutSequence (n K : ℕ) where
  cut : Fin (K+1) → CutRing
  strictMono : StrictMono (fun i => ordinary (cut i))
  length : Fin (K+1) → ℕ
  start : Fin (K+1) → ℤ
  length_le : ∀ i, length i ≤ n*9/10
  lower_label : ∀ i, start i ≤ endpointLabel (cut 0) ∧ endpointLabel (cut 0) < start i+length i
  upper_label : ∀ i, start i ≤ endpointLabel (cut (Fin.last K)) ∧ endpointLabel (cut (Fin.last K)) < start i+length i
  cut_label : ∀ i, start i ≤ endpointLabel (cut i) ∧ endpointLabel (cut i) < start i+length i

namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)

def index (_D : AxisCutSequence n K) (i : ℕ) : Fin (K+1) := ⟨min i K,by omega⟩
@[simp] theorem index_zero : D.index 0 = 0 := by ext; simp [index]
@[simp] theorem index_fin (i : Fin (K+1)) : D.index i.val = i := by ext; simp [index]; omega

theorem index_mono : Monotone D.index := by
  intro i j hij
  exact min_le_min_right K hij

theorem ordered (i : Fin (K+1)) :
    ordinary (D.cut 0) ≤ ordinary (D.cut i) ∧ ordinary (D.cut i) ≤ ordinary (D.cut (Fin.last K)) :=
  ⟨D.strictMono.monotone (Fin.zero_le i),D.strictMono.monotone (Fin.le_last i)⟩

theorem length_old (i : Fin (K+1)) : D.length i ≤ n := by have hh := D.length_le i; omega

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

noncomputable def anchorCopy : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length 0) (D.length_old 0) (D.start 0)
    (coordinateInterval a d (D.cut 0) (D.cut (Fin.last K)))

noncomputable def prefixCopy (i : ℕ) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length (D.index i)) (D.length_old _) (D.start (D.index i))
    (coordinateInterval a d (D.cut 0) (D.cut (D.index i)))

noncomputable def suffix (i : ℕ) : TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.axisSector hlarge n g d (D.length (D.index i)) (D.length_old _) (D.start (D.index i))
    (coordinateInterval a d (D.cut (D.index i)) (D.cut (Fin.last K)))

theorem anchorCopy_eq (i : Fin (K+1)) :
    D.anchorCopy B hlarge g d =
      B.axisSector hlarge n g d (D.length i) (D.length_old i) (D.start i)
        (coordinateInterval a d (D.cut 0) (D.cut (Fin.last K))) :=
  B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _
    (D.lower_label 0) (D.upper_label 0) (D.lower_label i) (D.upper_label i)

theorem prefix_suffix (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1) (i : ℕ)
    (s : TrackStar (Fin (m+1))) :
    D.anchorCopy B hlarge g d s = D.prefixCopy B hlarge g d i s*D.suffix B hlarge g d i s := by
  rw [D.anchorCopy_eq B hlarge g d (D.index i)]
  exact B.axisSector_split hlarge n g d _ _ _ _ _ _
    (D.ordered _).1 (D.ordered _).2 hlen (D.lower_label _) (D.cut_label _) s

@[simp] theorem prefix_zero : D.prefixCopy B hlarge g d 0 = 1 := by
  simp only [prefixCopy,index_zero,InitialCoverSystem.axisSector_self]

theorem prefix_last : D.prefixCopy B hlarge g d K = D.anchorCopy B hlarge g d := by
  have hi : D.index K = Fin.last K := by ext; simp [index]
  simp only [prefixCopy,hi]
  exact (D.anchorCopy_eq B hlarge g d (Fin.last K)).symm

theorem prefix_projection (i : ℕ) :
    (coverMap M (alternatingGenerator a r m hm)).comp (D.prefixCopy B hlarge g d i) =
      (conditionalAlternatingHom (coordinateInterval a d (D.cut 0) (D.cut (D.index i)))).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) :=
  B.axisSector_projection hlarge n g d _ _ _ _ _ (D.lower_label _) (D.cut_label _)

theorem suffix_projection (i : ℕ) :
    (coverMap M (alternatingGenerator a r m hm)).comp (D.suffix B hlarge g d i) =
      (conditionalAlternatingHom (coordinateInterval a d (D.cut (D.index i)) (D.cut (Fin.last K)))).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) :=
  B.axisSector_projection hlarge n g d _ _ _ _ _ (D.cut_label _) (D.upper_label _)

theorem prefix_small_supported (i : ℕ) :
    B.AlignedSmallSupported (D.prefixCopy B hlarge g d i) :=
  B.axisSector_supported hlarge n g d _ _ _ _
    (axisInterval_resolved d _ _ _ _ (D.lower_label _) (D.cut_label _))

theorem anchorCopy_small_supported : B.AlignedSmallSupported (D.anchorCopy B hlarge g d) :=
  B.axisSector_supported hlarge n g d _ _ _ _
    (axisInterval_resolved d _ _ _ _ (D.lower_label 0) (D.upper_label 0))

theorem prefix_small_controlled (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1) (i : ℕ) :
    SmallControlled B.c (D.prefixCopy B hlarge g d i) (D.anchorCopy B hlarge g d) := by
  rw [D.anchorCopy_eq B hlarge g d (D.index i)]
  exact B.fullGeometricSector_small_control hlarge _ _ _ _
    (coordinateInterval_mono d _ _ _ _ le_rfl (D.ordered _).1 (D.ordered _).2 hlen)

theorem prefix_suffix_self_commute (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1)
    (i : ℕ) (s t : TrackStar (Fin (m+1))) :
    Commute (D.prefixCopy B hlarge g d i s) (D.suffix B hlarge g d i t) :=
  B.axisSector_split_commute hlarge n g d _ _ _ _ _ _
    (D.ordered _).1 (D.ordered _).2 hlen (D.lower_label _) (D.cut_label _) s t

end AxisCutSequence
end AxisCutSequences

section NestedSupport
variable {α H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

variable (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (f : TrackStar α →* H) (l h : ℕ → TrackStar α →* H)
    (hf : ∀ i s, f s = l i s*h i s)
    (hc : ∀ i j, i ≤ j → ∀ s t, Commute (l i s) (h j t))

theorem cutDifference_small_supported (hs : ∀ i, SmallSupported L (l i)) (i : ℕ) :
    SmallSupported L (cutDifference f l h hf hc i) := by
  intro I x hx
  obtain ⟨s,rfl⟩ := hx
  change (l i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ *
    l (i+1) (universalMap (subtypeAlternatingHom I.val) s) ∈ L I.val
  exact (L I.val).mul_mem ((L I.val).inv_mem (hs i I ⟨s,rfl⟩)) (hs (i+1) I ⟨s,rfl⟩)

theorem cutDifference_small_controlled (hs : ∀ i, SmallControlled c (l i) f) (i : ℕ) :
    SmallControlled c (cutDifference f l h hf hc i) f := by
  intro I t x hx
  obtain ⟨s,rfl⟩ := hx
  apply (same_conj_iff _ _ _).mpr
  change Commute _ ((l i s)⁻¹*l (i+1) s)
  exact ((same_conj_iff _ _ _).mp (hs i I t _ ⟨s,rfl⟩)).inv_right.mul_right
    ((same_conj_iff _ _ _).mp (hs (i+1) I t _ ⟨s,rfl⟩))

end NestedSupport

end SimpleAmenable
end
end

end OAI
