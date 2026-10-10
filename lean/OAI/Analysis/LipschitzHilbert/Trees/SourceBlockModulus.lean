import OAI.Analysis.LipschitzHilbert.Estimates.ShiftedBlocks
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathCoefficientMotion

namespace OAI

/-! At a vertex of the phase simplex, a complete shifted source block
has only one nonunit transition modulus. Its coefficient is exactly the
child-to-boundary power used in the dominant-path comparison. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem source_shifted_block_norm {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (phase : Fin K → ℂ) (σ : Fin K) (j : ℕ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X) :
    ‖g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap
        (fun i => phase (ShiftedBlocks.tag hK i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (slope top)‖ =
    (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x /
      g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x) ^ (phase σ).re := by
  apply ShiftedBlocks.analytic_block_norm hK σ j g
    (fun level cell => g.mass tops slope precision cutoff weight level cell x)
    (fun level cell => g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell x)
    phase (slope top) hphase
  · intro i hi
    exact g.path_mass_pos tops slope precision cutoff weight hw (i+1) top htop
      (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hi).2; omega) he) x
  · intro i hi
    have hm := g.path_mass_pos tops slope precision cutoff weight hw (i+1) top htop
      (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hi).2; omega) he) x
    exact hm.trans_le (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) hK gap i (slope top) x).1

theorem source_shifted_block_mass_bounds {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (σ : Fin K) (j : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ≤
      g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) s) x := by
  have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp hw hK gap
    (ShiftedBlocks.lastTransition σ j) s x
  rw [← ShiftedBlocks.endpoint_eq_last_sub σ j] at hb
  simpa only [ShiftedBlocks.lastTransition_succ] using hb

theorem source_shifted_path_coefficient_eq {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (phase : Fin K → ℂ) (σ : Fin K) (j : ℕ) (μ r : ℝ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (hreal : (phase σ).re = μ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x
    let m := g.sourceBoundaryMass tops slope precision cutoff weight K gap
      (ShiftedBlocks.lastTransition σ j) (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x
    let lam := g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap
        (fun i => phase (ShiftedBlocks.tag hK i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (slope top)
    (c/n)^(1-μ-1/r)*‖lam‖ = pathCoefficient (1-μ-1/r) μ (c/n) (c/m) := by
  dsimp only
  rw [g.source_shifted_block_norm tops slope precision cutoff weight hp hw hK gap phase σ j
    hphase top htop he x,hreal]
  rfl

/-- The actual shifted-block coefficient inherits the complementary-mass
motion estimate, with the path drop left as a factor. -/
theorem source_shifted_path_coefficient_motion {ι : Type*} {Kb : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : Fin Kb → ℂ) (σ : Fin Kb) (j : ℕ)
    (μ r u : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hr : 1 ≤ r)
    (ha : 0 ≤ 1-μ-1/r)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (hreal : (phase σ).re = μ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ (j+1)))
    (h : ℕ) (hbase : h ≤ ShiftedBlocks.endpoint σ j)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (hblock : g.width h ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/2) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (T top).slope) x
    let c := fun x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (T top).slope) x
    let lam := fun x => g.packetPathProduct
      (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (fun i => phase (ShiftedBlocks.tag hKb i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (T top).slope
    let C := fun x => (c x/n x)^(1-μ-1/r)*‖lam x‖
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    1-c z/n z ≤ u →
    0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
      0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
      |C (SlopeBox.lineShift sR b z)-C z| ≤ 24*(Real.exp δ*δ)*u := by
  classical
  dsimp only
  intro hdrop
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let last := ShiftedBlocks.lastTransition σ j
  let parentSet := g.cellTops tops slope precision cutoff lo (g.index lo (slope top))
  let childSet := g.cellTops tops slope precision cutoff hi (g.index hi (slope top))
  let boundarySet := g.boundaryTops tops slope precision cutoff lo last (gap last) (slope top)
  let total := fun (A : Finset ι) x => ∑ t ∈ A, weight t x
  let C := fun x => (total childSet x/total parentSet x)^(1-μ-1/r)*
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight Kb gap
      (fun i => phase (ShiftedBlocks.tag hKb i)) x) lo hi (slope top)‖
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hlast : lo ≤ last := (Finset.mem_Ico.mp (ShiftedBlocks.lastTransition_mem hKb σ j)).1
  have hchildBoundary : childSet ⊆ boundarySet := by
    have hc := g.cellTops_subset_ancestor tops slope precision cutoff hp (Nat.le_succ last) (slope top)
    have hb0 := g.parent_subset_boundary tops slope precision cutoff lo last (gap last) (slope top)
    have hc' : childSet ⊆ g.cellTops tops slope precision cutoff last (g.index last (slope top)) := by
      simpa only [childSet,hi,last,Nat.succ_eq_add_one,ShiftedBlocks.lastTransition_succ] using hc
    exact hc'.trans hb0
  have hboundaryParent : boundarySet ⊆ parentSet :=
    g.boundary_subset_ancestor tops slope precision cutoff hp hlast (gap last) (slope top)
  have hne : childSet.Nonempty :=
    ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩⟩
  have hboundary (x : ℝ × ℝ) : g.sourceBoundaryMass tops slope precision cutoff weight Kb gap last
      (g.index hi (slope top)) x = total boundarySet x := by
    change g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
      (ShiftedBlocks.lastTransition σ j)
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x = total boundarySet x
    rw [← ShiftedBlocks.lastTransition_succ σ j,g.sourceBoundaryMass_path tops slope precision cutoff weight hKb,
      ← ShiftedBlocks.endpoint_eq_last_sub σ j]
    rfl
  have hC (x : ℝ × ℝ) : C x = pathCoefficient (1-μ-1/r) μ
      (total childSet x/total parentSet x) (total childSet x/total boundarySet x) := by
    have heq := g.source_shifted_path_coefficient_eq tops slope precision cutoff weight hp hwpos hKb gap
      phase σ j μ r hphase hreal top htop he x
    change C x = pathCoefficient (1-μ-1/r) μ
      (total childSet x/total parentSet x)
      (total childSet x/g.sourceBoundaryMass tops slope precision cutoff weight Kb gap last
        (g.index hi (slope top)) x) at heq
    rw [hboundary] at heq
    exact heq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hresult := g.source_path_coefficient_motion tops T w B Kw D hw hB hKw hD hwidth
    0 h lo hbase 0 (by norm_num) (g.width_pos h).le (slope top) sR hs
    (g.width hi) (g.width_pos hi) hblock parentSet boundarySet childSet hchildBoundary hboundaryParent hne
    (g.parent_subset_boundary tops slope precision cutoff 0 lo 0 (slope top)) b hb z
    (1-μ-1/r) μ u ha (by have : 0 ≤ 1/r := div_nonneg zero_le_one hr0.le; linarith)
    hμ0 hμ1 hsmall hdrop
  change 0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
    0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
    |C (SlopeBox.lineShift sR b z)-C z| ≤
      24*(Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
        ((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*u
  rw [hC z,hC (SlopeBox.lineShift sR b z)]
  exact hresult

end LipschitzHilbert.AngularGrid

end

end OAI
