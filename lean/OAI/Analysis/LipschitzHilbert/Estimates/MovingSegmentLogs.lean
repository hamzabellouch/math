import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceWeight
import OAI.Analysis.LipschitzHilbert.Phase.AngularMassMotion
import OAI.Analysis.LipschitzHilbert.Estimates.SegmentWeights

namespace OAI

/-! The initial value and loss budget for the actual moving segment
logarithms. The total cost is paid by the full-root loss, including when
another shift's block begins before the segment. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def segmentCost (n R : ℕ → ℝ) (a Z : ℝ) (j : ℕ) : ℝ :=
  a*Real.log (n j/n (j+1))+Z*R j

/-- At the starting endpoint the transition product is empty, so only
the one initial mass logarithm moves. -/
theorem segmentLog_initial_motion (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a delta : ℝ) (start : ℕ) (ha : 0 ≤ a)
    (hlog : |Real.log (n' start)-Real.log (n start)| ≤ delta) :
    ‖segmentLog n' R' phase a start start-segmentLog n R phase a start start‖ ≤ a*delta := by
  have heq : segmentLog n' R' phase a start start-segmentLog n R phase a start start =
      ((-a*(Real.log (n' start)-Real.log (n start)) : ℝ) : ℂ) := by
    simp only [segmentLog, Finset.Ico_self, Finset.sum_empty, sub_zero]
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hlog ha

theorem segmentCost_nonnegative (n R : ℕ → ℝ) (a Z : ℝ) (j : ℕ)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hn : 0 < n (j+1)) (hm : n (j+1) ≤ n j) (hR : 0 ≤ R j) :
    0 ≤ segmentCost n R a Z j := by
  exact add_nonneg (mul_nonneg ha (Real.log_nonneg ((one_le_div hn).mpr hm))) (mul_nonneg hZ hR)

theorem segmentLog_increment_le_cost (n R : ℕ → ℝ) (phase : ℕ → ℂ)
    (a Z : ℝ) (start j : ℕ) (hs : start ≤ j) (ha : 0 ≤ a) (_hZ : 0 ≤ Z)
    (hn : 0 < n (j+1)) (hm : n (j+1) ≤ n j) (hR : 0 ≤ R j) (hz : ‖phase j‖ ≤ Z) :
    ‖segmentLog n R phase a start (j+1)-segmentLog n R phase a start j‖ ≤
      segmentCost n R a Z j := by
  rw [segmentLog_increment n R phase a start j hs (hn.trans_le hm) hn]
  exact (logarithm_increment_bound a _ _ _ ha
    (Real.log_nonneg ((one_le_div hn).mpr hm)) hR).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hz hR))

/-- Summing the nonnegative costs on any later segment uses the full-root
logarithm rather than a factor counting hierarchy levels. -/
theorem segmentCost_sum_le_full_root (n R : ℕ → ℝ) (start N K : ℕ)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j+1-K)/n (j+1))) :
    (∑ j ∈ Finset.Ico start N, segmentCost n R a Z j) ≤
      (a+Z*K)*Real.log (n 0/n N) := by
  have hnonneg (j : ℕ) (hj : j < N) : 0 ≤ segmentCost n R a Z j :=
    segmentCost_nonnegative n R a Z j ha hZ (hn (j+1) (by omega))
      (hmono (by change j ≤ N; omega) (by change j+1 ≤ N; omega) (by omega)) (hR0 j hj)
  calc
    _ ≤ ∑ j ∈ Finset.range N, segmentCost n R a Z j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj _
        exact hnonneg j (Finset.mem_range.mp hj)
    _ = a*Real.log (n 0/n N)+Z*(∑ j ∈ Finset.range N, R j) := by
      simp only [segmentCost, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_log_ratios n N hn]
    _ ≤ a*Real.log (n 0/n N)+Z*((K:ℝ)*Real.log (n 0/n N)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (full_root_log_variation n R N K hn hmono hR) hZ)
    _ = _ := by ring

namespace AngularGrid

/-- The actual starting cell supplies the initial moving-log estimate.
The boundary-loss sequences do not enter at this endpoint. -/
theorem source_segment_initial_motion {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (h start : ℕ) (hh : h ≤ start) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) start)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (R0 R1 : ℕ → ℝ) (phase : ℕ → ℂ) (exponent : ℝ) (hexponent : 0 ≤ exponent) :
    let n := fun x j => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) (fun t x => (T t).weight K D x) j (g.index j (T top).slope) x
    ‖segmentLog (n (SlopeBox.lineShift sR a z)) R1 phase exponent start start -
      segmentLog (n z) R0 phase exponent start start‖ ≤
        exponent*((5*D/K)/Real.sqrt (g.branching:ℝ)) := by
  dsimp only
  apply segmentLog_initial_motion _ _ R0 R1 phase exponent _ start hexponent
  let A := g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
    (g.rootWidth/B^2) start (g.index start (T top).slope)
  have hA : A.Nonempty := by
    refine ⟨top,?_⟩
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
    0 h start hh gap hgap0 hgap (T top).slope sR hs child hchild hblock A hA
    (g.parent_subset_boundary tops _ _ _ 0 start gap (T top).slope) a ha z

/-- Actual eligible-top masses supply every initial-increment and budget
hypothesis for moving exponential segment weights. -/
theorem source_segment_log_budget {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (start N : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (x : X)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hphase : ∀ j < N, ‖phase j‖ ≤ Z) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let R := fun j => Real.log (g.sourceBoundaryMass tops slope precision cutoff weight
      K gap j (g.index (j+1) (slope top)) x / n (j+1))
    (∀ j < N, 0 ≤ segmentCost n R a Z j) ∧
    (∀ j ∈ Finset.Ico start N,
      ‖segmentLog n R phase a start (j+1)-segmentLog n R phase a start j‖ ≤ segmentCost n R a Z j) ∧
    (∑ j ∈ Finset.Ico start N, segmentCost n R a Z j) ≤ (a+Z*K)*Real.log (n 0/n N) := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let R := fun j => Real.log (g.sourceBoundaryMass tops slope precision cutoff weight
    K gap j (g.index (j+1) (slope top)) x/n (j+1))
  have hn (j : ℕ) (hj : j ≤ N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hm : Antitone n := g.path_mass_antitone tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) top x
  have hR0 (j : ℕ) (hj : j < N) : 0 ≤ R j := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j+1) (by omega))).mpr
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun t x => (hw t x).le) hK gap j (slope top) x).1
  have hR (j : ℕ) (hj : j < N) : R j ≤ Real.log (n (j+1-K)/n (j+1)) := by
    have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) hK gap j (slope top) x
    exact Real.log_le_log (div_pos ((hn (j+1) (by omega)).trans_le hb.1) (hn (j+1) (by omega)))
      (div_le_div_of_nonneg_right hb.2 (hn (j+1) (by omega)).le)
  refine ⟨?_,?_,?_⟩
  · intro j hj
    exact segmentCost_nonnegative n R a Z j ha hZ (hn (j+1) (by omega)) (hm (by omega)) (hR0 j hj)
  · intro j hj
    exact segmentLog_increment_le_cost n R phase a Z start j (Finset.mem_Ico.mp hj).1 ha hZ
      (hn (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega)) (hm (by omega))
      (hR0 j (Finset.mem_Ico.mp hj).2) (hphase j (Finset.mem_Ico.mp hj).2)
  · exact segmentCost_sum_le_full_root n R start N K a Z ha hZ hn (hm.antitoneOn _) hR0 hR

end AngularGrid
end LipschitzHilbert

end

end OAI
