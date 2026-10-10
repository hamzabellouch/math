import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteSectorPartition

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SeparatedAxisSectors

noncomputable def axisCellStripPair {n : ℕ} (d : Fin 2)
    (k k' l : ℕ) (hk : k ≤ n) (hk' : k' ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p p' q : ℤ) (u v u' v' : CutRing)
    (huv : ordinary u ≤ ordinary v) (hgap : ordinary v < ordinary u')
    (huv' : ordinary u' ≤ ordinary v')
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
    (hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k')
    (hkn : k ≤ n*9/10) (hkn' : k' ≤ n*9/10) (hln : l ≤ n/4) (i : Fin l) : OldStripPair n d where
  left := axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i
  right := axisCellRectangle d k' l hk' hl hlpos p' q u' v' huv' hu' hv' i
  lo := u
  cutLeft := v
  cutRight := u'
  hi := v'
  bottom := windowCut l q i.castSucc
  top := windowCut l q i.succ
  left_lower _ := rfl
  left_upper _ := rfl
  right_lower _ := rfl
  right_upper _ := rfl
  ordered_left := huv
  ordered_gap := hgap
  ordered_right := huv'
  ordered_cross := (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  left_length j := by change (if j=d then k else l) ≤ _; split <;> assumption
  right_length j := by change (if j=d then k' else l) ≤ _; split <;> assumption

theorem transverse_window_mesh (n : ℕ) (hn : 1005 ≤ n) (q : ℤ) (i : Fin (n/4)) :
    ordinary (windowCut (n/4) q i.succ)-ordinary (windowCut (n/4) q i.castSucc) ≤ 1000/(n:ℝ) := by
  apply (windowCut_mesh (n/4) q i).trans
  have hp : (0:ℝ) < ((n/4:ℕ):ℝ) := by exact_mod_cast (show 0 < n/4 by omega)
  have hnp : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : (n:ℝ) ≤ 5*((n/4:ℕ):ℝ) := by exact_mod_cast (show n ≤ 5*(n/4) by omega)
  apply (div_le_div_iff₀ hp hnp).mpr
  linarith

namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem separated_axis_sectors_commute (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (k k' : ℕ) (hk : k ≤ n*9/10) (hk' : k' ≤ n*9/10)
      (p p' : ℤ) (u v u' v' : CutRing)
      (_huv : ordinary u ≤ ordinary v) (_hgap : ordinary v < ordinary u')
      (_huv' : ordinary u' ≤ ordinary v')
      (_hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
      (_hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
      (_hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
      (_hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k'),
      ordinary v'-ordinary u ≤ C/(n:ℝ) →
      |(endpointLabel (u'-v):ℝ)| ≤ 6*(n:ℝ)/5 →
      ∀ x y, Commute
        (B.axisSector (by omega) n g d k (by omega) p (coordinateInterval a d u v) x)
        (B.axisSector (by omega) n g d k' (by omega) p' (coordinateInterval a d u' v') y) := by
  obtain ⟨N₀,hN₀,hcomm⟩ := separated_old_rectangles_commute
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort (by linarith : 0 ≤ C) hSlope hconj
  refine ⟨max 1005 N₀,by omega,?_⟩
  intro M B h n hn g d k k' hk hk' p p' u v u' v' huv hgap huv' hu hv hu' hv' hwidth hlabels x y
  have hnpos : 1005 ≤ n := by omega
  let f (i : Fin (n/4)) := B.rectangleCopy (by omega) g
    (axisCellRectangle d k (n/4) (by omega) (by omega) (by omega) p 0 u v huv hu hv i)
  let f' (i : Fin (n/4)) := B.rectangleCopy (by omega) g
    (axisCellRectangle d k' (n/4) (by omega) (by omega) (by omega) p' 0 u' v' huv' hu' hv' i)
  have hc (i j : Fin (n/4)) (x y : TrackStar (Fin (m+1))) : Commute (f i x) (f' j y) := by
    by_cases hij : i=j
    · subst j
      let P := axisCellStripPair d k k' (n/4) (by omega) (by omega) (by omega) (by omega)
        p p' 0 u v u' v' huv hgap huv' hu hv hu' hv' hk hk' le_rfl i
      exact hcomm M B h n (by omega) g d P hwidth
        ((transverse_window_mesh n hnpos 0 i).trans
          (div_le_div_of_nonneg_right hC (by positivity))) hlabels x y
    · exact B.axisCellRectangle_distinct_commute hlarge n g d k k' (n/4)
        (by omega) (by omega) (by omega) (by omega) p p' 0 u v u' v' huv huv' hu hv hu' hv' i j hij x y
  exact commute_of_range_iSup f f' hc
    (B.axisSector_range_cells (by omega) n g d k (n/4) (by omega) (by omega) (by omega)
      p 0 u v huv hu hv ⟨x,rfl⟩)
    (B.axisSector_range_cells (by omega) n g d k' (n/4) (by omega) (by omega) (by omega)
      p' 0 u' v' huv' hu' hv' ⟨y,rfl⟩)

end InitialCoverSystem
end SeparatedAxisSectors

section AxisCoherence

@[simp] theorem coordinateInterval_self {a : ℕ} (d : Fin 2) (u : CutRing) :
    coordinateInterval a d u u = ⊥ := by
  apply Subtype.ext
  exact coordinateBetween_empty d u u (by simp)

noncomputable def endpointPairStart (u v : CutRing) : ℤ := min (endpointLabel u) (endpointLabel v)
noncomputable def endpointPairLength (u v : CutRing) : ℕ :=
  (max (endpointLabel u) (endpointLabel v)-endpointPairStart u v).toNat+1

theorem endpointPairLength_cast (u v : CutRing) :
    (endpointPairLength u v : ℤ) = max (endpointLabel u) (endpointLabel v)-endpointPairStart u v+1 := by
  have hh : 0 ≤ max (endpointLabel u) (endpointLabel v)-endpointPairStart u v := by
    simp only [endpointPairStart]; omega
  simp only [endpointPairLength,Nat.cast_add,Nat.cast_one,Int.toNat_of_nonneg hh]

theorem endpointPair_labels (u v : CutRing) :
    (endpointPairStart u v ≤ endpointLabel u ∧ endpointLabel u < endpointPairStart u v+endpointPairLength u v) ∧
    (endpointPairStart u v ≤ endpointLabel v ∧ endpointLabel v < endpointPairStart u v+endpointPairLength u v) := by
  rw [endpointPairLength_cast]
  simp only [endpointPairStart]
  omega

theorem endpointPair_in_window (u v : CutRing) (p : ℤ) (k : ℕ)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    p ≤ endpointPairStart u v ∧ endpointPairStart u v+endpointPairLength u v ≤ p+k ∧
      endpointPairLength u v ≤ k := by
  have hh := endpointPairLength_cast u v
  simp only [endpointPairStart] at hh ⊢
  omega

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_subwindow (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q : ℤ)
    (hs : p ≤ q) (he : q+l ≤ p+k) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (axisWindowPrimitives d k p) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (axisWindowPrimitives d l q) i).val) V.val) :
    B.axisSector hlarge n g d k hk p V = B.axisSector hlarge n g d l hl q V := by
  rw [B.axisSector_in_window hlarge n g d k hk p (fun _ => p) le_rfl (by omega) V hV,
    B.axisSector_in_window hlarge n g d l hl q (fun _ => p) hs (by omega) V hV']

theorem axisInterval_copy_eq (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q : ℤ) (u v : CutRing)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : q ≤ endpointLabel u ∧ endpointLabel u < q+l)
    (hv' : q ≤ endpointLabel v ∧ endpointLabel v < q+l) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) =
      B.axisSector hlarge n g d l hl q (coordinateInterval a d u v) := by
  have hp := endpointPair_in_window u v p k hu hv
  have hq := endpointPair_in_window u v q l hu' hv'
  have hend := endpointPair_labels u v
  rw [B.axisSector_subwindow hlarge n g d k (endpointPairLength u v) hk (by omega)
      p (endpointPairStart u v) hp.1 hp.2.1 _ (axisInterval_resolved d k p u v hu hv)
      (axisInterval_resolved d _ _ u v hend.1 hend.2),
    B.axisSector_subwindow hlarge n g d l (endpointPairLength u v) hl (by omega)
      q (endpointPairStart u v) hq.1 hq.2.1 _ (axisInterval_resolved d l q u v hu' hv')
      (axisInterval_resolved d _ _ u v hend.1 hend.2)]

@[simp] theorem fullGeometricSector_bot {ι : Type*} [Finite ι] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    B.fullGeometricSector hlarge P h ⊥ = 1 := by
  unfold fullGeometricSector
  have he : resolvedPolygonMask (primitiveTests (a := a) (r := r) P) (⊥ : polygonAlgebra a).val = ∅ := by
    ext ω
    simp [resolvedPolygonMask]
  rw [he,ActualLawfulTable.sector_empty]

@[simp] theorem axisSector_self (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u : CutRing) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u u) = 1 := by
  rw [coordinateInterval_self]
  exact B.fullGeometricSector_bot hlarge _ _

theorem axisSector_projection (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v : CutRing)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    (coverMap M (alternatingGenerator a r m hm)).comp
      (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v)) =
      (conditionalAlternatingHom (coordinateInterval a d u v)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) :=
  B.fullGeometricSector_projection hlarge _ _ _ (axisInterval_resolved d k p u v hu hv)

end InitialCoverSystem
end AxisCoherence

end SimpleAmenable
end
end

end OAI
