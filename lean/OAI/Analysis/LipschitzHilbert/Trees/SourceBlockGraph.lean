import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockChildren
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales

namespace OAI

/-! The exact eligible-top block family supplies the graph input of the
source predictor. Its boundary masses and transition moduli are the ones
in the shared analytic amplitude. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

/-- The transition coefficient on each actual child satisfies the graph
bound with the actual source boundary mass. -/
theorem source_block_coefficient_bounds {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → (ℝ × ℝ) → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t z, 0 < weight t z) {Kb : ℕ} (hKb : 0 < Kb)
    (gap : ℕ → ℝ) (phase : Fin Kb → ℂ) (σ : Fin Kb) (j : ℕ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (μ : ℝ) (hμ : 0 ≤ μ)
    (hreal : (phase σ).re = μ) (parent : ℤ) (z : ℝ × ℝ) :
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
    let m := fun i : cells => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
      (ShiftedBlocks.lastTransition σ j) i.val z
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight Kb gap
        (fun k => phase (ShiftedBlocks.tag hKb k)) z) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))
    (∀ i, ‖lam i‖ = (c i/m i)^μ) ∧ (∀ i, ‖lam i‖ ≤ 1) := by
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have heq (i : cells) := g.source_shifted_block_norm tops slope precision cutoff weight hp hw
    hKb gap phase σ j hphase (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).1
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.1 z
  have hindex (i : cells) :=
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.2
  dsimp only [lower,upper] at hindex heq
  have hnorm (i : cells) :
      ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight Kb gap
        (fun k => phase (ShiftedBlocks.tag hKb k)) z) lower upper
          (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))‖ =
      (g.mass tops slope precision cutoff weight upper i.val z /
        g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
          (ShiftedBlocks.lastTransition σ j) i.val z)^μ := by
    simpa only [hreal,hindex i] using heq i
  refine ⟨hnorm,?_⟩
  intro i
  have hc := g.path_mass_pos tops slope precision cutoff weight hw upper
    (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).1
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.1 z
  have hb := (g.source_shifted_block_mass_bounds tops slope precision cutoff weight
    hp (fun t z => (hw t z).le) hKb gap σ j
    (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)) z).1
  dsimp only [lower,upper] at hc hb
  rw [hindex i] at hc hb
  rw [hnorm]
  exact Real.rpow_le_one (div_pos hc (hc.trans_le hb)).le
    ((div_le_one (hc.trans_le hb)).mpr hb) hμ

/-- All positivity, graph-mass, separated-frequency, and supported-count
premises follow from the actual shifted block and the separated-top count. -/
theorem source_block_graph_data {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (L : ℝ) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ)
    (tops : Finset ι) (T : ι → SlopeBox) (w : ℝ) (hw : 0 < w)
    (weight : ι → (ℝ × ℝ) → ℝ) (hweight : ∀ t z, 0 < weight t z)
    (parent : ℤ) (z : ℝ × ℝ)
    (path : g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) parent)
    (A : g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) parent → EuclideanSpace ℂ κ)
    (K D c0 sR : ℝ) (hD : 2 ≤ D) (hc0 : SourceParameters.step L^(-(1/8:ℝ)) ≤ c0)
    (eta : κ → ℝ) (heta : ∀ k, c0/w ≤ |eta k|)
    (hsmall : ∀ c,
      (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/(SourceParameters.branching L)^2) (ShiftedBlocks.endpoint σ (j+1)) c.val,
        K < (T t).radius z) →
      ‖A c‖ ≤ 2*SourceParameters.step L^(-(1/8:ℝ))*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/(SourceParameters.branching L)^2) weight
          (ShiftedBlocks.endpoint σ (j+1)) c.val z)
    (hcount : ∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ K) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤
        SourceParameters.branching L*g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ D/100) :
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cells := g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) lower upper parent
    let c := fun i : cells => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight upper i.val z
    let n := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower parent z
    let m := fun i : cells => g.boundaryMass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower (ShiftedBlocks.lastTransition σ j)
      (g.sourceGap L upper) ((T (g.sourceBlockTop tops (fun t => (T t).slope)
        (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2) lower upper parent i)).slope) z
    let G := fun i k : cells => g.neighbors upper (g.sourceGap L upper) i.val k.val
    let f := fun i k => (sR-g.center upper i.val)*eta k
    (∀ i, 0 < c i) ∧ 0 < n ∧ (∑ i, c i/n) ≤ 1 ∧
    (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) ∧
    (∀ i k, i ≠ k → ¬G i k → ∀ v,
      1/(sourceLineScale g L w upper*SourceParameters.step L^(-(1/8:ℝ))) ≤ |f i v-f k v|) ∧
    (∀ S : Finset cells,
      (∀ i ∈ S, radialShrink (2*SourceParameters.step L^(-(1/8:ℝ))*c i) (A i) ≠ 0 ∨ i = path) →
      (S:Set cells).Pairwise (fun i k => ¬G i k) → (S.card:ℝ) ≤ D) := by
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/(SourceParameters.branching L)^2
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let last := ShiftedBlocks.lastTransition σ j
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun i : cells =>
    slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i
  have hscales := g.source_shifted_count_scales L hbranch hKb σ j
  have hc00 : 0 ≤ c0 := (Real.rpow_nonneg (SourceParameters.step_pos L).le _).trans hc0
  have hlast : lower ≤ last := (Finset.mem_Ico.mp (ShiftedBlocks.lastTransition_mem hKb σ j)).1
  have hresult := g.source_angular_prediction_data (sR := sR) tops T precision cutoff weight
    (fun t _ => (div_pos hw (T t).length_pos).le) hweight z lower last hlast parent cells
    representative (fun i => by simpa only [last,upper,representative,ShiftedBlocks.lastTransition_succ] using (hrep i).2.2.2)
    (fun i => (hrep i).2.1)
    (fun i => by simpa only [last,upper,ShiftedBlocks.lastTransition_succ] using
      g.sourceBlockCells_nonempty_child tops slope precision cutoff lower upper parent i)
    path A (g.sourceGap_pos L upper) hD
    (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
    (by simpa only [cutoff,last,upper,ShiftedBlocks.lastTransition_succ] using hscales.1)
    hscales.2 (by simpa only [last,upper,ShiftedBlocks.lastTransition_succ] using hsmall)
    hcount eta (div_nonneg hc00 hw.le) heta
    (source_line_fourier_threshold g L hw upper hc0)
  simpa only [last,upper,lower,representative,ShiftedBlocks.lastTransition_succ] using hresult

end LipschitzHilbert.AngularGrid

end

end OAI
