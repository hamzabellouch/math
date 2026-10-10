import OAI.Analysis.LipschitzHilbert.Estimates.MovingSegmentWeights
import OAI.Analysis.LipschitzHilbert.Phase.AngularPathLossMotion

namespace OAI

/-! Moving endpoint weights for the actual source masses. Every motion
hypothesis is derived from the physical top weights and angular locality. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem source_moving_weight_variation {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hKw : 0 < Kw) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start M : ℕ) (hstart : start ≤ M) (hbase : h ≤ start)
    (hgap : ∀ j, h ≤ j → j ≤ M → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) M)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hZ : 0 ≤ Z) (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : (T top).weight Kw D z ≤ C) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun x k => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight k (g.index k (T top).slope) x
    let m := fun x k => g.sourceBoundaryMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap k
      (g.index (k+1) (T top).slope) x
    let z' := SlopeBox.lineShift sR b z
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let ε := Real.exp (2*δ)-1
    ‖segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start M-
        segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start M‖ +
      (∑ j ∈ Finset.Ico start M,
        ‖(segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start (j+1)-
            segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start (j+1))-
          (segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start j-
            segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start j)‖) ≤
      Real.exp (a*δ)*(δ+ε)*C^4*
        (1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2*
        (weight top z)^(-(4:ℝ)) := by
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let n := fun x k => g.mass tops slope precision cutoff weight k (g.index k (T top).slope) x
  let m := fun x k => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap k
    (g.index (k+1) (T top).slope) x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let ε := Real.exp (2*δ)-1
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hweight (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hmasspos (x : ℝ × ℝ) (j : ℕ) (hj : j ≤ M) : 0 < n x j :=
    g.path_mass_pos tops slope precision cutoff weight hweight j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hlower (j : ℕ) (hj : j ≤ M) : weight top z ≤ n z j := by
    apply Finset.single_le_sum (fun t _ => (hweight t z).le)
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hj he⟩
  have hmono (x : ℝ × ℝ) : Antitone (n x) :=
    g.path_mass_antitone tops slope precision cutoff weight hp (fun t x => (hweight t x).le) top x
  have hmbounds (x : ℝ × ℝ) (j : ℕ) :
      n x (j+1) ≤ m x j ∧ m x j ≤ n x (j+1-Kb) :=
    g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hweight t x).le) hKb gap j (T top).slope x
  have hR0 (x : ℝ × ℝ) (j : ℕ) (hj : j < M) : 0 ≤ boundaryLog (n x) (m x) j :=
    boundaryLog_nonnegative (n x) (m x) j (hmasspos x (j+1) (by omega)) (hmbounds x j).1
  have hR (j : ℕ) (hj : j < M) : boundaryLog (n z) (m z) j ≤
      Real.log (n z (j+1-Kb)/n z (j+1)) :=
    boundaryLog_le_root_ratio (n z) (m z) j Kb (hmasspos z (j+1) (by omega))
      ((hmasspos z (j+1) (by omega)).trans_le (hmbounds z j).1) (hmbounds z j).2
  have hmass (j : ℕ) (hjs : start ≤ j) (hjM : j ≤ M) :
      |Real.log (n z' j)-Real.log (n z j)| ≤ δ := by
    let A := g.cellTops tops slope precision cutoff j (g.index j (T top).slope)
    have hA : A.Nonempty := ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hjM he⟩⟩
    exact g.boundary_submass_source_motion tops T w B Kw D hw hB hKw hD hwidth
      0 h j (hbase.trans hjs) (gap j) (hgap j (hbase.trans hjs) hjM).1
      (hgap j (hbase.trans hjs) hjM).2 (T top).slope sR hs child hchild hblock A hA
      (g.parent_subset_boundary tops slope precision cutoff 0 j (gap j) (T top).slope) b hb z
  have hloss (j : ℕ) (hj : j ∈ Finset.Ico start M) :=
    g.source_path_loss_motion tops T w B Kw D hw hB hKw hD hwidth hKb gap h j
      (hbase.trans (Finset.mem_Ico.mp hj).1)
      (hgap j (hbase.trans (Finset.mem_Ico.mp hj).1) (Nat.le_of_lt (Finset.mem_Ico.mp hj).2)).1
      (hgap j (hbase.trans (Finset.mem_Ico.mp hj).1) (Nat.le_of_lt (Finset.mem_Ico.mp hj).2)).2
      top htop (g.eligible_of_le (hp top htop)
        (by have := (Finset.mem_Ico.mp hj).2; omega) he) sR hs child hchild hblock b hb z
  have hv := moving_segmentWeight_variation (n z) (n z') (boundaryLog (n z) (m z))
    (boundaryLog (n z') (m z')) phase start M Kb hstart a Z δ ε (weight top z)
    ha0 hZ hδ hε (hweight top z) hlower (hmasspos z') ((hmono z).antitoneOn _)
    (hR0 z) (hR0 z') hR hz0 hz hmass (fun j hj => (hloss j hj).1)
    (fun j hj => (hloss j hj).2)
  have htotal : n z 0 ≤ ∑ t ∈ tops, weight t z :=
    g.mass_le_total tops slope precision cutoff weight (fun t x => (hweight t x).le) 0 _ z
  have hS : weight top z ≤ ∑ t ∈ tops, weight t z := (hlower 0 (Nat.zero_le M)).trans htotal
  have hQ : 0 ≤ a+Z*Kb := by positivity
  have hV : 0 ≤ (a+Z*Kb)*Real.log (n z 0/n z M) := by
    apply mul_nonneg hQ
    exact Real.log_nonneg ((one_le_div (hmasspos z M le_rfl)).mpr (hmono z (Nat.zero_le M)))
  have hVQ : (a+Z*Kb)*Real.log (n z 0/n z M) ≤
      (a+Z*Kb)*Real.log ((∑ t ∈ tops, weight t z)/weight top z) := by
    apply mul_le_mul_of_nonneg_left _ hQ
    apply Real.log_le_log (div_pos (hmasspos z 0 (Nat.zero_le M)) (hmasspos z M le_rfl))
    exact (div_le_div_of_nonneg_right htotal (hmasspos z M le_rfl).le).trans
      (div_le_div_of_nonneg_left ((hweight top z).le.trans hS) (hweight top z) (hlower M le_rfl))
  exact moving_weight_budget_absorption (hweight top z) hS hC htC hQ ha0 ha1
    hδ hε hV hVQ hv

end LipschitzHilbert.AngularGrid

end

end OAI
