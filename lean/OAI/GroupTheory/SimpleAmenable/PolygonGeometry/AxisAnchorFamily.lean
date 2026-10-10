import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.DisjointPolygonAtoms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SortedAxisCuts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AxisAnchorFamily

structure AxisAnchorFamily (n l : ℕ) (q : ℤ) where
  count : Fin l → ℕ
  cuts : ∀ i, AxisCutSequence n (count i)
  lower : ∀ i, (cuts i).cut 0 = windowCut l q i.castSucc
  upper : ∀ i, (cuts i).cut (Fin.last (count i)) = windowCut l q i.succ

namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)

theorem intervalLength (hl : 201 ≤ l) (i : Fin l) :
    ordinary ((A.cuts i).cut (Fin.last (A.count i)))-ordinary ((A.cuts i).cut 0) < 1 := by
  rw [A.lower,A.upper]
  have hl' : (200:ℝ) < l := by exact_mod_cast (show 200 < l by omega)
  exact (windowCut_mesh l q i).trans_lt ((div_lt_one (by linarith)).mpr hl')

theorem atom_le_cell {a : ℕ} (d : Fin 2) (hl : 201 ≤ l) (i : Fin l) (j : Fin (A.count i)) :
    (A.cuts i).atomPolygon (a := a) d j ≤ windowCell a d l q i := by
  have h₁ := (A.cuts i).ordered j.castSucc
  have h₂ := (A.cuts i).ordered j.succ
  change coordinateInterval a d _ _ ≤ coordinateInterval a d _ _
  rw [← A.lower,← A.upper]
  exact coordinateInterval_mono d _ _ _ _ h₁.1
    ((A.cuts i).strictMono (Fin.castSucc_lt_succ (i := j))).le h₂.2 (A.intervalLength hl i)

theorem atom_disjoint {a : ℕ} (d : Fin 2) (hl : 201 ≤ l) :
    Pairwise fun i j : (Σ i : Fin l, Fin (A.count i)) =>
      Disjoint ((A.cuts i.1).atomPolygon (a := a) d i.2).val ((A.cuts j.1).atomPolygon d j.2).val := by
  rintro ⟨i,k⟩ ⟨j,k'⟩ hij
  by_cases he : i=j
  · subst j
    apply (A.cuts i).atomPolygon_disjoint d (A.intervalLength hl i)
    intro hk
    change k=k' at hk
    subst k'
    exact hij rfl
  · exact (windowCell_pairwise_disjoint d l (by omega) q he).mono
      (A.atom_le_cell d hl i k) (A.atom_le_cell d hl j k')

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (hl : 201 ≤ l) (hln : l ≤ n)

include hl in
theorem anchorCopy_eq_cell (i : Fin l) :
    (A.cuts i).anchorCopy B hlarge g d = B.axisSector hlarge n g d l hln q (windowCell a d l q i) := by
  change B.axisSector hlarge n g d _ _ _ (coordinateInterval a d _ _) =
    B.axisSector hlarge n g d l hln q (coordinateInterval a d _ _)
  rw [← A.lower,← A.upper]
  apply B.axisInterval_copy_eq
  · exact (A.cuts i).lower_label 0
  · exact (A.cuts i).upper_label 0
  · rw [A.lower]; exact windowCut_label l q (by omega) _
  · rw [A.upper]; exact windowCut_label l q (by omega) _

include hl hln in
theorem anchorCopies_commute {i j : Fin l} (hij : i ≠ j) (x y : TrackStar (Fin (m+1))) :
    Commute ((A.cuts i).anchorCopy B hlarge g d x) ((A.cuts j).anchorCopy B hlarge g d y) := by
  rw [A.anchorCopy_eq_cell B hlarge g d hl hln i,A.anchorCopy_eq_cell B hlarge g d hl hln j]
  exact B.fullGeometricSector_commute hlarge _ _ _ _
    (windowCell_axis_resolved d l (by omega) q i) (windowCell_pairwise_disjoint d l (by omega) q hij) x y

variable (hc : ∀ (i : Fin l) (j k : ℕ), j ≤ k → ∀ x y,
  Commute ((A.cuts i).prefixCopy B hlarge g d j x) ((A.cuts i).suffix B hlarge g d k y))

include hl hln in
theorem atoms_commute (h20 : 20 ≤ m+1) :
    Pairwise fun i j : (Σ i : Fin l, Fin (A.count i)) => ∀ x y,
      Commute ((A.cuts i.1).atomCopy B hlarge g d (A.intervalLength hl i.1) (hc i.1) i.2 x)
        ((A.cuts j.1).atomCopy B hlarge g d (A.intervalLength hl j.1) (hc j.1) j.2 y) := by
  rintro ⟨i,k⟩ ⟨j,k'⟩ hij x y
  by_cases he : i=j
  · subst j
    apply (A.cuts i).atomCopy_commute B hlarge g d (A.intervalLength hl i) (hc i)
    · intro hk; change k=k' at hk; subst k'; exact hij rfl
  · apply small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned (by simpa using h20)
      _ _ ((A.cuts i).anchorCopy B hlarge g d) ((A.cuts j).anchorCopy B hlarge g d)
    · exact (A.cuts i).atomCopy_supported B hlarge g d (A.intervalLength hl i) (hc i) k
    · exact (A.cuts j).atomCopy_supported B hlarge g d (A.intervalLength hl j) (hc j) k'
    · exact (A.cuts i).anchorCopy_small_supported B hlarge g d
    · exact (A.cuts i).atomCopy_controlled B hlarge g d (A.intervalLength hl i) (hc i) k
    · exact (A.cuts j).atomCopy_controlled B hlarge g d (A.intervalLength hl j) (hc j) k'
    · exact A.anchorCopies_commute B hlarge g d hl hln he

include hl hln hc in

theorem prefixes_central (h20 : 20 ≤ m+1) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (⨆ i : Fin l, ⨆ j : Fin (A.count i+1), ((A.cuts i).prefixCopy B hlarge g d j.val).range) := by
  let f (i : Σ i : Fin l, Fin (A.count i)) :=
    (A.cuts i.1).atomCopy B hlarge g d (A.intervalLength hl i.1) (hc i.1) i.2
  have hcentral := centralOn_disjoint_polygon_atoms
    (coverMap M (alternatingGenerator a r m hm))
    (fun i : Σ i : Fin l, Fin (A.count i) => (A.cuts i.1).atomPolygon d i.2)
    (A.atom_disjoint d hl)
    (fun i => (A.cuts i.1).atomPolygon_nonempty d (A.intervalLength hl i.1) i.2)
    f (A.atoms_commute B hlarge g d hl hln hc h20)
    (fun i => (A.cuts i.1).atomCopy_projection B hlarge g d (A.intervalLength hl i.1) (hc i.1) i.2)
  apply hcentral.mono
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  apply (prefix_range_le_differences ((A.cuts i).anchorCopy B hlarge g d) _ _
    ((A.cuts i).prefix_suffix B hlarge g d (A.intervalLength hl i)) (hc i)
    ((A.cuts i).prefix_zero B hlarge g d) (A.count i) j.val (by omega)).trans
  apply iSup_le
  intro k
  exact le_iSup (fun z => (f z).range) ⟨i,k⟩

end AxisAnchorFamily
end AxisAnchorFamily

section GrowthAnchors
attribute [local instance] cutOrdinaryOrder

def growthOldLength (n : ℕ) := n*9/10

def growthNewLength (n : ℕ) := n*6/5

def growthAnchorLength (n : ℕ) := 2*growthOldLength n-growthNewLength n

def growthAnchorStart (n : ℕ) (p : ℤ) := p+(growthNewLength n:ℤ)-growthOldLength n

theorem growth_lengths {n : ℕ} (hn : 1005 ≤ n) :
    growthOldLength n ≤ n ∧ growthOldLength n ≤ growthNewLength n ∧
    growthNewLength n ≤ 2*growthOldLength n ∧ 201 ≤ growthAnchorLength n ∧
    growthAnchorLength n ≤ n ∧ n ≤ 2*growthAnchorLength n := by
  simp only [growthAnchorLength,growthOldLength,growthNewLength]
  omega

theorem growth_anchor_label {n : ℕ} (hn : 1005 ≤ n) (p : ℤ) (i : Fin (growthAnchorLength n+1)) :
    p+(growthNewLength n:ℤ)-growthOldLength n ≤ endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) ∧
    endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) < p+growthOldLength n := by
  have h := windowCut_label (growthAnchorLength n) (growthAnchorStart n p) (by have := growth_lengths hn; omega) i
  have hh := growth_lengths hn
  have he : (growthAnchorLength n:ℤ) = 2*(growthOldLength n:ℤ)-growthNewLength n := by
    unfold growthAnchorLength
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  unfold growthAnchorStart at h ⊢
  rw [he] at h
  omega

noncomputable def growthAnchorFamily (n : ℕ) (hn : 1005 ≤ n) (p : ℤ) :
    AxisAnchorFamily n (growthAnchorLength n) (growthAnchorStart n p) := by
  let l := growthAnchorLength n
  let q := growthAnchorStart n p
  let u (i : Fin l) := windowCut l q i.castSucc
  let v (i : Fin l) := windowCut l q i.succ
  let S (i : Fin l) := anchorCutSet (growthNewLength n) p (u i) (v i)
  have hlens := growth_lengths hn
  have hl (i : Fin l) : ordinary (u i) ≤ ordinary (v i) :=
    (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  have hu (i : Fin l) := growth_anchor_label hn p i.castSucc
  have hv (i : Fin l) := growth_anchor_label hn p i.succ
  have hu' (i : Fin l) : p ≤ endpointLabel (u i) ∧ endpointLabel (u i) < p+growthNewLength n := by
    have := hu i; dsimp [u,l,q]; constructor <;> omega
  have hv' (i : Fin l) : p ≤ endpointLabel (v i) ∧ endpointLabel (v i) < p+growthNewLength n := by
    have := hv i; dsimp [v,l,q]; constructor <;> omega
  let D (i : Fin l) := sortedAxisCutSequence n (growthOldLength n) (growthNewLength n) p (u i) (v i) (S i)
    (anchorCutSet_lower _ _ _ _) (anchorCutSet_upper _ _ _ _)
    (anchorCutSet_bounds _ _ _ _ (hl i)) (anchorCutSet_labels _ _ _ _ (hu' i) (hv' i))
    (hu i) (hv i) hlens.2.1 hlens.2.2.1 (by rfl)
  exact ⟨fun i => (S i).card-1,D,fun i => sortedAxisCutSequence_lower ..,
    fun i => sortedAxisCutSequence_upper ..⟩

namespace growthAnchorFamily
variable (n : ℕ) (hn : 1005 ≤ n) (p : ℤ)
local notation "A" => growthAnchorFamily n hn p

theorem length (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    ((A).cuts i).length j = growthOldLength n := rfl

theorem start (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    ((A).cuts i).start j = if endpointLabel (((A).cuts i).cut j)<p+growthOldLength n then p
      else growthAnchorStart n p := rfl

theorem mem (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    ((A).cuts i).cut j ∈ anchorCutSet (growthNewLength n) p
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.castSucc)
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.succ) :=
  Finset.orderEmbOfFin_mem _ _ j

theorem range (i : Fin (growthAnchorLength n)) :
    Set.range ((A).cuts i).cut = (anchorCutSet (growthNewLength n) p
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.castSucc)
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.succ) : Set CutRing) :=
  Finset.range_orderEmbOfFin _ _

theorem labels (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    p ≤ endpointLabel (((A).cuts i).cut j) ∧ endpointLabel (((A).cuts i).cut j) < p+growthNewLength n := by
  apply anchorCutSet_labels _ _ _ _ ?_ ?_ _ (mem n hn p i j)
  · have hh := growth_anchor_label hn p i.castSucc
    have hlens := growth_lengths hn
    constructor <;> omega
  · have hh := growth_anchor_label hn p i.succ
    have hlens := growth_lengths hn
    constructor <;> omega

theorem label_difference (i : Fin (growthAnchorLength n)) (j k : Fin ((A).count i+1)) :
    |(endpointLabel (((A).cuts i).cut k-((A).cuts i).cut j):ℝ)| ≤ 6*(n:ℝ)/5 := by
  have hj := labels n hn p i j
  have hk := labels n hn p i k
  have hh : growthNewLength n*5 ≤ n*6 := by unfold growthNewLength; omega
  rw [endpointLabel_sub,Int.cast_sub]
  have hj' : (p:ℝ) ≤ endpointLabel (((A).cuts i).cut j) ∧
    (endpointLabel (((A).cuts i).cut j):ℝ) < (p:ℝ)+growthNewLength n := by exact_mod_cast hj
  have hk' : (p:ℝ) ≤ endpointLabel (((A).cuts i).cut k) ∧
    (endpointLabel (((A).cuts i).cut k):ℝ) < (p:ℝ)+growthNewLength n := by exact_mod_cast hk
  have hh' : (growthNewLength n:ℝ)*5 ≤ (n:ℝ)*6 := by exact_mod_cast hh
  rw [abs_le]; constructor <;> linarith

theorem width (i : Fin (growthAnchorLength n)) :
    ordinary (((A).cuts i).cut (Fin.last ((A).count i)))-ordinary (((A).cuts i).cut 0) ≤ 400/(n:ℝ) := by
  rw [(A).lower,(A).upper]
  apply (windowCut_mesh _ _ i).trans
  have hh := growth_lengths hn
  have hpos : (0:ℝ) < growthAnchorLength n := by exact_mod_cast (show 0 < growthAnchorLength n by omega)
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n:ℝ) ≤ 2*growthAnchorLength n := by exact_mod_cast hh.2.2.2.2.2
  apply (div_le_div_iff₀ hpos hn').mpr
  linarith

end growthAnchorFamily
end GrowthAnchors

end SimpleAmenable
end
end

end OAI
