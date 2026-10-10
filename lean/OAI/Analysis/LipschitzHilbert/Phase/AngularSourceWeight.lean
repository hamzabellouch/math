import OAI.Analysis.LipschitzHilbert.Phase.AngularAnalyticWeight
import OAI.Analysis.LipschitzHilbert.Phase.AngularStopping
import OAI.Analysis.LipschitzHilbert.Trees.HierarchyWeights

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

def sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (level : ℕ) (cell : ℤ) (x : X) : ℝ :=
  g.boundaryMass tops slope precision cutoff weight (level+1-K) level
    (gap level) (g.center (level+1) cell) x

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

/-- The source's full-root logarithmic bound follows from actual top
masses, including all losses of eligibility. -/
theorem source_full_root_log_variation (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : ι)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (x : X) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let R := fun j => Real.log (g.sourceBoundaryMass tops slope precision cutoff weight
      K gap j (g.index (j+1) (slope top)) x / n (j+1))
    (∑ j ∈ Finset.range N, R j) ≤ (K : ℝ) * Real.log (n 0 / n N) := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  have hn (j : ℕ) (hj : j ≤ N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hm := g.path_mass_antitone tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) top x
  apply full_root_log_variation n _ N K hn (hm.antitoneOn _)
  intro j hj
  have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap j (slope top) x
  have hjN : j+1 ≤ N := by omega
  have hmpos := (hn (j+1) hjN).trans_le hb.1
  exact Real.log_le_log (div_pos hmpos (hn (j+1) hjN))
    (div_le_div_of_nonneg_right hb.2 (hn (j+1) hjN).le)

/-- No positive lower cutoff on a mass is imposed: the assigned top's
own weight supplies the endpoint bound. -/
theorem source_hierarchyWeight_variation (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (N : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (x : X)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < N, 0 ≤ (phase j).re) (hz : ∀ j < N, ‖phase j‖ ≤ Z) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let R := fun j => Real.log (g.sourceBoundaryMass tops slope precision cutoff weight
      K gap j (g.index (j+1) (slope top)) x / n (j+1))
    ‖hierarchyWeight n R phase a N‖ +
      (∑ j ∈ Finset.range N, ‖hierarchyWeight n R phase a (j+1) - hierarchyWeight n R phase a j‖) ≤
      (weight top x)^(-a) * (1+(a+Z*K)*Real.log (n 0 / n N)) := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  have hn (j : ℕ) (hj : j ≤ N) : weight top x ≤ n j := by
    apply Finset.single_le_sum (fun i _ => (hw i x).le)
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop, rfl, g.eligible_of_le (hp top htop) hj he⟩
  have hnpos (j : ℕ) (hj : j ≤ N) : 0 < n j := (hw top x).trans_le (hn j hj)
  have hm := g.path_mass_antitone tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) top x
  apply hierarchyWeight_variation n _ phase N K a (weight top x) Z ha (hw top x) hZ hn
    (hm.antitoneOn _)
  · intro j hj
    have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun i x => (hw i x).le) hK gap j (slope top) x
    exact Real.log_nonneg ((one_le_div (hnpos (j+1) (by omega))).mpr hb.1)
  · intro j hj
    have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun i x => (hw i x).le) hK gap j (slope top) x
    exact Real.log_le_log (div_pos ((hnpos (j+1) (by omega)).trans_le hb.1)
      (hnpos (j+1) (by omega)))
      (div_le_div_of_nonneg_right hb.2 (hnpos (j+1) (by omega)).le)
  · exact hz0
  · exact hz

end LipschitzHilbert.AngularGrid

end

end OAI
