import OAI.Analysis.LipschitzHilbert.Phase.AngularPathNormalization

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

def sourceTransition (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X) :
    ℕ → ℤ → ℂ :=
  analyticTransition (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x) phase

def sourcePacketBase (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : σ → E) (a : ℝ) (x : X) (s : σ) : E :=
  ((g.mass tops slope precision cutoff weight (stop s)
    (g.index (stop s) (slope (assigned s))) x ^ (-a) : ℝ) : ℂ) • value s

def sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) : E :=
  g.packetAmplitude packets (fun s => slope (assigned s)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x) level cell

theorem sourceTransition_norm_le_one (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (x : X) (level : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (level+1)) (hz : 0 ≤ (phase level).re) :
    ‖g.sourceTransition tops slope precision cutoff weight K gap phase x level
      (g.index (level+1) (slope top))‖ ≤ 1 := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw (level+1) top htop he x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap level (slope top) x).1
  exact analyticTransition_norm_le_one _ _ phase level _ hn (hn.trans_le hb) hb hz

theorem sourceBoundaryMass_parent_le (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  exact (g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x).2.1

/-- At equal real coordinates the packet coefficient is precisely the
product of the parent-to-boundary ratios from the manuscript. -/
theorem source_normalized_endpoint (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : ι)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight
      K gap j (g.index (j+1) (slope top)) x
    ((n 0^a : ℝ) : ℂ) * (((n N^(-a) : ℝ) : ℂ) *
      g.packetPathProduct
        (g.sourceTransition tops slope precision cutoff weight K gap (fun _ => (a : ℂ)) x)
        0 N (slope top)) = ((∏ j ∈ Finset.range N, (n j / b j)^a : ℝ) : ℂ) := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight
    K gap j (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j ≤ N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hb (j : ℕ) (hj : j < N) : 0 < b j :=
    (hn (j+1) (by omega)).trans_le
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun i x => (hw i x).le) hK gap j (slope top) x).1
  have hpath := hierarchyWeight_eq_path_product n b (fun _ => (a : ℂ)) a N
    (hn N le_rfl) (fun j hj => hn (j+1) (by omega)) hb
  have hnorm := normalized_endpoint_telescope n b a N hn hb
  rw [hpath] at hnorm
  simpa only [packetPathProduct, Nat.Ico_zero_eq_range, sourceTransition, analyticTransition]
    using hnorm

/-- Boundary coefficients always lie in the unit interval. -/
theorem source_boundary_product_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : ι)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N)
    (a : ℝ) (ha : 0 ≤ a) (x : X) :
    let c := ∏ j ∈ Finset.range N,
      (g.mass tops slope precision cutoff weight j (g.index j (slope top)) x /
        g.sourceBoundaryMass tops slope precision cutoff weight K gap j
          (g.index (j+1) (slope top)) x)^a
    0 < c ∧ c ≤ 1 := by
  dsimp only
  have hn (j : ℕ) (hj : j ≤ N) := g.path_mass_pos tops slope precision cutoff weight hw
    j top htop (g.eligible_of_le (hp top htop) hj he) x
  have hb (j : ℕ) := g.sourceBoundaryMass_parent_le tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap j (slope top) x
  constructor
  · apply Finset.prod_pos
    intro j hj
    have hjN : j ≤ N := Nat.le_of_lt (Finset.mem_range.mp hj)
    exact Real.rpow_pos_of_pos (div_pos (hn j hjN) ((hn j hjN).trans_le (hb j))) a
  · apply Finset.prod_le_one₀
    · intro j hj
      have hjN : j ≤ N := Nat.le_of_lt (Finset.mem_range.mp hj)
      exact Real.rpow_nonneg (div_nonneg (hn j hjN).le ((hn j hjN).trans_le (hb j)).le) a
    · intro j hj
      have hjN : j ≤ N := Nat.le_of_lt (Finset.mem_range.mp hj)
      exact Real.rpow_le_one (div_nonneg (hn j hjN).le ((hn j hjN).trans_le (hb j)).le)
        ((div_le_one ((hn j hjN).trans_le (hb j))).mpr (hb j)) ha

end LipschitzHilbert.AngularGrid

end

end OAI
