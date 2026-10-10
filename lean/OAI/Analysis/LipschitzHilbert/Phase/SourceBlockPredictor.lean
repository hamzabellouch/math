import OAI.Analysis.LipschitzHilbert.Trees.SourceEitherGrid
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockGraph
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotAmplitudeScale

namespace OAI

/-! Apply the normalized predictor to actual eligible-top block masses,
canonical top representatives, and coefficients of the shared source family. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_block_predictor (C Q Cfreq c0 : ℝ)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 2 ≤ D → 0 < N → Real.log N ≤ 2*L →
    ∀ (ι κ : Type) [DecidableEq ι] [Fintype κ]
      (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ)
      (tops : Finset ι) (T : ι → SlopeBox) (w : ℝ) (hw : 0 < w),
    ∀ (weight : ι → (ℝ × ℝ) → ℝ), (∀ t z, 0 < weight t z) →
    ∀ (parent : ℤ) (z : ℝ × ℝ) (origin sR : ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ),
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cutoff := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let representative := fun i : cells => slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
    let n := g.mass tops slope precision cutoff weight lower parent z
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) z)
      lower upper (representative i)
    let p := Real.sqrt L
    let μ := phaseMu D p
    let ε := SourceParameters.step L^(-(1/8:ℝ))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ (i₀ : cells) (A : cells → EuclideanSpace ℂ κ) (K u q : ℝ),
      0 ≤ u → n ≤ L^C*N → (∀ i, ‖A i‖ ≤ L^Q*c i) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i : cells, (∀ t ∈ g.cellTops tops slope precision cutoff upper i.val,
        K < (T t).radius z) → ‖A i‖ ≤ 2*ε*c i) →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ K) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → cells → ℝ) (A' : ℝ → cells → EuclideanSpace ℂ κ)
      (lam' : ℝ → cells → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (μ-1+1/p) • A' b i-
          diagonalModulation (fun k => (sR-g.center upper i.val)*eta k)
            (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^μ) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(μ-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(μ-1):ℝ):ℂ) • (lam i •
            diagonalModulation (fun k => (sR-g.center upper i.val)*eta k) (A i) b)‖ ≤
          ε*(L^(Q+C)*(1+N^μ))*(c i/n)) →
      (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
        0 ≤ (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ∧
        (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 1 ∧
        1-(c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 2*u ∧
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-μ-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-μ-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p μ (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually (gt_mem_nhds hc0)
  filter_upwards [eventually_source_grid_parameters (Q+C) (2*Cfreq) (by positivity) (by positivity),
    hsmall,eventually_ge_atTop (256:ℝ)] with L hgrid hsmall hL
  intro D N hD hN hlog ι κ _ _ g hbranch hKb σ j tops T w hw weight hweight parent z origin sR eta
    hetaLo hetaHi phase hphase hreal
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/(SourceParameters.branching L)^2
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun i : cells => slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
  let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
  let n := g.mass tops slope precision cutoff weight lower parent z
  let m := fun i : cells => g.boundaryMass tops slope precision cutoff weight lower
    (ShiftedBlocks.lastTransition σ j) (g.sourceGap L upper) (representative i) z
  let lam := fun i : cells => g.packetPathProduct
    (g.sourceTransition tops slope precision cutoff weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) z)
    lower upper (representative i)
  let p := Real.sqrt L
  let μ := phaseMu D p
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  let frequency := fun i : cells => fun k => (sR-g.center upper i.val)*eta k
  let freqBound := (2*Cfreq)*g.width lower/w
  intro i₀ A K u q hu hmass hA hoff hzero hcount n' c' A' lam' hn' hc' hscaled hnum hdom
  have hlu : lower ≤ upper := (ShiftedBlocks.endpoint_strictMono hKb σ).monotone (Nat.le_succ j)
  obtain ⟨hc,hn,htotal,hm,hsep,hcard⟩ := g.source_block_graph_data L hbranch hKb σ j tops T w hw
    weight hweight parent z i₀ A K D c0 sR hD hsmall.le eta hetaLo hzero hcount
  have hμ := source_phaseMu_small (show 1 ≤ D by linarith) hL
  have hsize := source_snapshot_amplitude_scale (show 1 ≤ L by linarith) hN hn hC hQ
    hμ.1.le (by linarith : μ ≤ 1) hmass
  have hcoefficient := g.source_block_coefficient_bounds tops slope precision cutoff weight
    (fun t _ => (div_pos hw (T t).length_pos).le) hweight hKb (g.sourceBoundaryGap L)
    phase σ j hphase μ hμ.1.le hreal parent z
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i
  have hmeq (i : cells) :
      g.sourceBoundaryMass tops slope precision cutoff weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (ShiftedBlocks.lastTransition σ j) i.val z = m i := by
    have h := g.source_shifted_boundary_mass L hbranch tops slope precision cutoff weight hKb σ j
      (representative i) z
    have hi : g.index (ShiftedBlocks.endpoint σ (j+1)) (representative i) = i.val := (hrep i).2.2.2
    rwa [hi] at h
  have hlam : ∀ i : cells, ‖lam i‖ ≤ 1 := hcoefficient.2
  have hlamGraph : ∀ i : cells, ‖lam i‖ ≤ (c i/m i)^μ := by
    intro i
    have h := hcoefficient.1 i
    dsimp only at h
    rw [hmeq i] at h
    exact h.le
  have hfreq : 0 ≤ freqBound := by
    dsimp [freqBound]
    exact div_nonneg (mul_nonneg (by positivity) (g.width_pos lower).le) hw.le
  have hspread (i : RemainderIndex i₀) (k : κ) :
      |frequency i.val k-frequency i₀ k| ≤ freqBound := by
    have hcenters := g.centers_close_in_ancestor hlu (representative i.val) (representative i₀)
      ((hrep i.val).2.1.trans (hrep i₀).2.1.symm)
    rw [(hrep i.val).2.2.2,(hrep i₀).2.2.2] at hcenters
    calc
      _ = |g.center upper i.val.val-g.center upper i₀.val| * |eta k| := by
        dsimp only [frequency]
        rw [show (sR-g.center upper i.val.val)*eta k-(sR-g.center upper i₀.val)*eta k =
          -(g.center upper i.val.val-g.center upper i₀.val)*eta k by ring,abs_mul,abs_neg]
      _ ≤ (2*g.width lower)*(Cfreq/w) := mul_le_mul hcenters (hetaHi k)
        (abs_nonneg _) (mul_nonneg (by norm_num) (g.width_pos lower).le)
      _ = freqBound := by dsimp only [freqBound]; ring
  have hmesh : freqBound*(grid.width/(grid.branching:ℝ)^(upper-lower)) ≤
      (2*Cfreq)*SourceParameters.step L^(-(1/16:ℝ)) := by
    have h := source_block_line_carrier g L origin hw lower upper hlu hbranch
      (le_refl ((2*Cfreq)*g.width lower/w))
    apply h.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (by norm_num : -(1/2:ℝ) ≤ -(1/16:ℝ)))
      (by positivity)
  let : DecidableEq cells := fun a b => Classical.propDecidable (a = b)
  have hm' : ∀ i : cells, orderMass c
      (closedNeighborhood (fun i k : cells => g.neighbors upper (g.sourceGap L upper) i.val k.val) i) ≤ m i := by
    intro i
    convert hm i using 1
    congr 1
    ext k
    simp only [mem_closedNeighborhood]
    rfl
  have hoff' : (∑ i : RemainderIndex i₀, c i/n) ≤ u := by
    convert hoff using 1
    congr 1
    ext i
    simp only [Finset.mem_univ]
  exact hgrid D N (by linarith) hN hlog cells κ grid (upper-lower) le_rfl
    (fun i k => g.neighbors upper (g.sourceGap L upper) i.val k.val)
    (fun _ _ h => g.neighbors_symmetric upper (g.sourceGap L upper) h) c m n hc hn hm' htotal frequency A lam i₀
    (L^Q) freqBound u q (Real.rpow_nonneg (by linarith) _) hfreq hu hsize.1 hsize.2
    hA hlam hlamGraph hoff' hsep hcard hspread hmesh n' c' A' lam' hn' hc' hscaled hnum hdom

end LipschitzHilbert.AngularGrid

end

end OAI
