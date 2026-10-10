import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeVertexMoment
import OAI.Analysis.LipschitzHilbert.Trees.SourceVertexConstantBudget

namespace OAI

/-! The actual finite source tree, with polynomial node and path costs,
provides the small-imaginary vertex moment in §11. Constants are fixed
before the finite packet family or the spatial good set is chosen. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

theorem eventually_source_tree_vertex_moment (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (μ : Measure X)
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
      (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
    ∀ (phase : ℕ → ℂ) (a alpha : ℝ), 1 ≤ alpha → alpha ≤ 3 →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (shift : Fin Kb) (count : ℕ) (cell : ℤ)
      (good : Set X), MeasurableSet good → ∀ (bad : τ → Set X),
      (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty →
      (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
        ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count)) →
    let p := Real.sqrt L
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ x ∈ good, ∀ j ≤ count, ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) c‖ ≤
        L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) c x) →
    (∀ x ∈ good, cost*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x)) μ) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ)) →
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
    let amp := fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell
    IntegrableOn (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
        L^(2*q+1)*(∑ t ∈ g.cellTops tops slope precision cutoff
          (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ)^(1/p) := by
  filter_upwards [eventually_source_vertex_constant_budget q A B (2*Pconst)
    hq hA hB (by positivity),eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets assigned stop
    value hv phase a alpha ha ha3 Kb hKb shift count cell good hgood bad hne hterminal
    p cost henvelope hbad hpathInt hpathBound n amp
  have hp0 : 0 < p := Real.sqrt_pos.mpr (zero_lt_one.trans_le hL)
  have hM : 1 ≤ L^A := Real.one_le_rpow hL hA
  have hC : 0 ≤ L^q := Real.rpow_nonneg (zero_le_one.trans hL) _
  obtain ⟨hi,hbound⟩ := g.source_packet_vertex_moment μ tops slope precision cutoff weight hp hw
    hwint hwmeas K gap packets assigned stop value hv phase a alpha p hKb shift count cell
    (L^A) (L^q) (Pconst*L^B*cost) hM hC ha hp0 good hgood bad hne hterminal
    henvelope hbad hpathInt hpathBound
  let S := ∑ t ∈ g.cellTops tops slope precision cutoff
    (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have heq : cost*(1+2*(Pconst*L^B*cost)) = cost*(1+(2*Pconst)*L^B*cost) := by ring
  have hbudget' : (cost*(1+(2*Pconst)*L^B*cost))^(1/p) ≤ L^(2*q+1) :=
    hbudget alpha ha ha3
  refine ⟨hi,?_⟩
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^(2*q+1)*S^(1/p)
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
    (cost*(1+2*(Pconst*L^B*cost))*S)^(1/p) at hbound
  rw [heq,Real.mul_rpow (mul_nonneg hcost (by positivity)) hS] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hbudget' (Real.rpow_nonneg hS _))

end LipschitzHilbert.AngularGrid

end

end OAI
