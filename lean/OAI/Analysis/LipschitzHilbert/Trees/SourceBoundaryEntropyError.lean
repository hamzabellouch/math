import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryTotalError
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryEntropy

namespace OAI

/-! The actual top-weight entropy converts the expected packet error
into a multiple of the total top mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_error_mass (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (T : τ → SlopeBox) (w cutoff Kw D : ℝ)
    (hw : 0 < w) (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (M : τ → ℕ) (he : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) (M t))
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ×ℝ) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : σ → E) (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (A H : ℝ) (hA : 0 ≤ A)
    (hlog : Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H)
    (hB : ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value s‖ ≤
        A*((T t).weight Kw D x)^8) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖(∑ s ∈ packets, value s)-
      ∑ s ∈ packets, (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        (8*a*A*epsilon*((2:ℝ)^D)^7*(1+H))*(∑ t ∈ tops, (T t).weight Kw D x) := by
  intro epsilon err
  have hb := g.source_boundary_expected_total_error L hbranch hsmall tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x)
    (fun t _ => (div_pos hw (T t).length_pos).le) (fun t x => (T t).weight_pos hKw D x)
    hK M he a ha x packets assigned hassigned stop value hmax
    (fun t => A*((T t).weight Kw D x)^8)
    (fun t _ => mul_nonneg hA (pow_nonneg ((T t).weight_pos hKw D x).le _)) hB
  refine ⟨hb.1,hb.2.trans ?_⟩
  have heq : (∑ t ∈ tops, (A*((T t).weight Kw D x)^8)*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D x)/(T t).weight Kw D x)) =
      A*(∑ t ∈ tops, ((T t).weight Kw D x)^8*
        Real.log ((∑ u ∈ tops, (T u).weight Kw D x)/(T t).weight Kw D x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [heq]
  have hc : 0 ≤ 8*a*epsilon*A := by
    dsimp only [epsilon]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _)).le) hA
  have h := mul_le_mul_of_nonneg_left (top_weight_boundary_entropy_sum_le_log_bound tops T hKw hD x hlog) hc
  convert h using 1 <;> ring

end LipschitzHilbert.AngularGrid

end

end OAI
