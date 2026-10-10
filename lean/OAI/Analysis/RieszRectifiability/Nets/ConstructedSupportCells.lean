import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ClosedNetCellCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def supportLatticeNets {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : SeparatedCover μ.support (latticeRadius R k) :=
  nestedSeparatedCovers μ.support (latticeRadius R) (latticeRadius_pos R hR)
    (fun j => latticeRadius_antitone R hR.le (Nat.le_succ j)) k

def supportLatticeCenter {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : μ.support :=
  ⟨z, (supportLatticeNets μ R hR k).subset z.property⟩

def supportLatticeCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : Set (Ambient d) :=
  closedNetCell (supportLatticeNets μ R hR) k (supportLatticeCenter μ R hR k z)

def supportLatticeAncestor {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    (supportLatticeNets μ R hR k).points :=
  ⟨netAncestor (supportLatticeNets μ R hR) k t (supportLatticeCenter μ R hR (k + t) z),
    netAncestor_consistent_on_net R (supportLatticeNets μ R hR) k t _ z.property⟩

theorem supportLatticeNets_monotone {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) :
    Monotone (fun k => (supportLatticeNets μ R hR k).points) :=
  nestedSeparatedCovers_monotone μ.support (latticeRadius R) (latticeRadius_pos R hR)
    (fun j => latticeRadius_antitone R hR.le (Nat.le_succ j))

theorem supportLatticeNets_countable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : (supportLatticeNets μ R hR k).points.Countable :=
  separated_set_countable _ _ (latticeRadius_pos R hR k) (supportLatticeNets μ R hR k).separated

theorem supportLatticeCell_closed {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsClosed (supportLatticeCell μ R hR k z) :=
  closedNetCell_isClosed _ _ _

theorem supportLatticeCell_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : supportLatticeCell μ R hR k z ⊆ μ.support :=
  closedNetCell_subset _ μ.isClosed_support _ _

theorem supportLatticeCell_bounds {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8) ⊆ supportLatticeCell μ R hR k z ∧
      supportLatticeCell μ R hR k z ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) := by
  constructor
  · exact relative_ball_subset_closedNetCell R hR (supportLatticeNets μ R hR) k
      (supportLatticeCenter μ R hR k z) z.property
  · exact closedNetCell_subset_closedBall R hR (supportLatticeNets μ R hR) k
      (supportLatticeCenter μ R hR k z)

theorem supportLatticeCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ supportLatticeCell μ R hR k z := by
  obtain ⟨z, hz, hcell⟩ := exists_closedNetCell_containing R hR (supportLatticeNets μ R hR) k ⟨x, hx⟩
  exact ⟨⟨z, hz⟩, hcell⟩

theorem supportLatticeCell_nested {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    supportLatticeCell μ R hR (k + t) z ⊆
      supportLatticeCell μ R hR k (supportLatticeAncestor μ R hR k t z) :=
  closedNetCell_nested _ k t _ _ rfl

theorem supportLatticeCell_compact {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsCompact (supportLatticeCell μ R hR k z) :=
  (isCompact_closedBall (z : Ambient d) (2 * latticeRadius R k)).of_isClosed_subset
    (supportLatticeCell_closed μ R hR k z) (supportLatticeCell_bounds μ R hR k z).2

theorem supportLatticeCell_measure_bounds {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (supportLatticeCell μ R hR k z) ∧
      μ (supportLatticeCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  have hball : μ (μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8)) =
      μ (ball (z : Ambient d) (latticeRadius R k / 8)) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    change (x ∈ μ.support ∧ x ∈ ball (z : Ambient d) (latticeRadius R k / 8)) ↔
      x ∈ ball (z : Ambient d) (latticeRadius R k / 8)
    simp only [hx, true_and]
  constructor
  · calc
      _ ≤ μ (ball (z : Ambient d) (latticeRadius R k / 8)) :=
        hlower z ((supportLatticeNets μ R hR k).subset z.property) _ hcore
      _ = _ := hball.symm
      _ ≤ _ := measure_mono (supportLatticeCell_bounds μ R hR k z).1
  · have hsub : closedBall (z : Ambient d) (2 * latticeRadius R k) ⊆
        ball (z : Ambient d) (3 * latticeRadius R k) :=
      closedBall_subset_ball (by have hp := latticeRadius_pos R hR k; linarith)
    apply (measure_mono ((supportLatticeCell_bounds μ R hR k z).2.trans hsub)).trans
    exact hg.2 z _ (mul_pos (by norm_num) (latticeRadius_pos R hR k))

end

end RieszRectifiability

end OAI
