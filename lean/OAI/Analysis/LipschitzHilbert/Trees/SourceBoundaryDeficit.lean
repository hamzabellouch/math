import OAI.Analysis.LipschitzHilbert.Phase.AngularAmplitudeIdentity

namespace OAI

/-! The exact central coefficient loses at most the sum of the logarithmic
parent-to-boundary losses. Its deficit grows with the packet stopping level. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

def sourceBoundaryLogLoss (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (N : ℕ) (top : τ) (x : X) : ℝ :=
  ∑ j ∈ Finset.range N, Real.log
    (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope top)) x /
      g.mass tops slope precision cutoff weight j (g.index j (slope top)) x)

theorem sourceBoundaryCoefficient_eq_exp (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x =
      Real.exp (-a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x) := by
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
    (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j < N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) (Nat.le_of_lt hj) he) x
  have hb (j : ℕ) (hj : j < N) : 0 < b j :=
    (hn j hj).trans_le (g.sourceBoundaryMass_parent_le tops slope precision cutoff weight
      hp (fun t x => (hw t x).le) hK gap j (slope top) x)
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      (n j/b j)^a = Real.exp (-a*Real.log (b j/n j)) := by
    have hjN := Finset.mem_range.mp hj
    rw [Real.rpow_def_of_pos (div_pos (hn j hjN) (hb j hjN)),
      Real.log_div (hn j hjN).ne' (hb j hjN).ne',
      Real.log_div (hb j hjN).ne' (hn j hjN).ne']
    congr 1
    ring
  change (∏ j ∈ Finset.range N, (n j/b j)^a) =
    Real.exp (-a*∑ j ∈ Finset.range N, Real.log (b j/n j))
  rw [Finset.prod_congr rfl hterm,← Real.exp_sum,Finset.mul_sum]

theorem sourceBoundaryLogLoss_mono (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) M) (x : X) :
    g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x ≤
      g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap M top x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
  intro j hj _
  have hn := g.path_mass_pos tops slope precision cutoff weight hw j top htop
    (g.eligible_of_le (hp top htop) (Nat.le_of_lt (Finset.mem_range.mp hj)) he) x
  apply Real.log_nonneg
  exact (one_le_div hn).mpr (g.sourceBoundaryMass_parent_le tops slope precision cutoff weight
    hp (fun t x => (hw t x).le) hK gap j (slope top) x)

theorem sourceBoundaryCoefficient_deficit_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ≤
      a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x := by
  rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top
    htop he a x]
  have h := Real.add_one_le_exp
    (-a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x)
  linarith

theorem sourceBoundaryCoefficient_antitone (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) M)
    (a : ℝ) (ha : 0 ≤ a) (x : X) :
    g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap M top a x ≤
      g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x := by
  rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap M top
      htop he a x,
    g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top
      htop (g.eligible_of_le (hp top htop) hNM he) a x]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (g.sourceBoundaryLogLoss_mono tops slope precision cutoff weight hp hw hK gap hNM top htop he x)
    (neg_nonpos.mpr ha)

end LipschitzHilbert.AngularGrid

end

end OAI
