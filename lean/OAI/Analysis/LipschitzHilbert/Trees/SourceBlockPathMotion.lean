import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionParameters

namespace OAI

/-! The actual shifted source coefficients supply every dominant-path
motion premise. The relative drop is retained even when it is zero. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid

 theorem eventually_source_block_path_motion (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ), ((ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j:ℕ):ℝ) ≤ L^2 →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (Z μ p u : ℝ),
      0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) → (phase σ).re = μ →
      0 ≤ μ → μ ≤ 1 → 1 ≤ p → 0 ≤ 1-μ-1/p → 0 ≤ u →
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ (j+1)) →
    ∀ (sR : ℝ), g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR →
    ∀ (z : ℝ × ℝ),
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let weight := fun t zz => (T t).weight Kw D zz
    let n := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower (g.index lower (T top).slope) zz
    let c := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight upper (g.index upper (T top).slope) zz
    let lam := fun zz => g.packetPathProduct
      (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/(SourceParameters.branching L)^2) weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (T top).slope
    let coeff := fun zz => (c zz/n zz)^(1-μ-1/p)*‖lam zz‖
    1-c z/n z ≤ u →
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ q ≤ SourceParameters.step L^(-(1/8:ℝ)) ∧
      lam z ≠ 0 ∧ 0 ≤ coeff z ∧ coeff z ≤ 1 ∧ 1-coeff z ≤ 2*u ∧
      ∀ b : ℝ, |b| ≤ sourceLineScale g L w upper →
        ‖lam (SlopeBox.lineShift sR b z)-lam z‖ ≤ q*‖lam z‖ ∧
        |coeff (SlopeBox.lineShift sR b z)-coeff z| ≤
          24*SourceParameters.step L^(-(1/8:ℝ))*u := by
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_source_path_errors_small D hD,hsmall] with L herrors hsmall
  intro ι g tops T w Kw hw hKw hbranch hwidth hKb σ j hsteps phase Z μ p u
    hZ0 hZ hphase hother hreal hμ0 hμ1 hp ha hu top htop he sR hs z
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
  let e := (upper-lower:ℕ)*Z*(2*δ)
  let q := Real.exp e*e
  have herror := herrors Kw Z (upper-lower) hKw hZ0 hZ hsteps
  have hB : 1 ≤ SourceParameters.branching L := by
    exact one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hblock := (g.source_shifted_width_bounds L hbranch hKb σ j).2
  have hq0 : 0 ≤ q := by dsimp [q,e,δ]; positivity
  have hqε : q ≤ SourceParameters.step L^(-(1/8:ℝ)) := herror.2
  have hq1 : q < 1 := hqε.trans_lt hsmall
  intro hdrop
  have hcoef := g.source_shifted_path_coefficient_motion tops T w (SourceParameters.branching L)
    Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
    phase σ j μ p u hμ0 hμ1 hp ha hother hreal top htop he lower le_rfl sR hs
    hblock 0 (by
      rw [abs_zero]
      exact (div_pos hw (mul_pos (g.width_pos _)
        (Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) g.branching_ge_two)))).le) z
    (by simpa only [hbranch] using herror.1.1.trans (by norm_num : (1/8:ℝ)≤1/2)) hdrop
  dsimp only at hcoef
  refine ⟨q,hq0,hq1,hqε,?_,hcoef.1.le,hcoef.2.1,hcoef.2.2.1,?_⟩
  · exact g.source_path_product_ne_zero _ _ _ _ _ _ _ _ _ _ _ _
  · intro b hb
    have hb' : |b| ≤ w/(g.width upper*Real.sqrt (g.branching:ℝ)) := by
      simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hb
    have hrelative := g.source_block_transition_relative_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
      (fun k => phase (ShiftedBlocks.tag hKb k)) lower lower upper le_rfl
      (fun k hk => ⟨(g.sourceBoundaryGap_pos L k).le,
        g.sourceBoundaryGap_le_width L (Finset.mem_Ico.mp hk).1⟩)
      top htop he sR hs (g.width upper) (g.width_pos upper) hblock b hb' z Z hZ0
      (fun k _ => hphase (ShiftedBlocks.tag hKb k))
    have hmove := g.source_shifted_path_coefficient_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
      phase σ j μ p u hμ0 hμ1 hp ha hother hreal top htop he lower le_rfl sR hs
      hblock b hb' z
      (by simpa only [hbranch] using herror.1.1.trans (by norm_num : (1/8:ℝ)≤1/2)) hdrop
    refine ⟨?_,hmove.2.2.2.2.2.trans ?_⟩
    · exact complex_relative_motion_to_sub
        (g.source_path_product_ne_zero _ _ _ _ _ _ _ _ _ _ _ _)
        (by simpa only [hbranch] using hrelative)
    · simpa only [hbranch] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herror.1.2 (by norm_num : (0:ℝ)≤24)) hu

end LipschitzHilbert.AngularGrid

end

end OAI
