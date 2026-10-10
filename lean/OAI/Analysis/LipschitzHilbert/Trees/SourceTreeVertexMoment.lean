import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeVertexIntegral

namespace OAI

/-! The actual finite packet-tree estimate yields the normalized root
Lp moment on the common good set, with no abstract terminal flow input. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem source_packet_vertex_moment (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hwint : ∀ t ∈ tops, Integrable (weight t) μ)
    (hwmeas : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ q, Measurable (fun x => value x q)) (phase : ℕ → ℂ) (a α p : ℝ)
    {Kb : ℕ} (hKb : 0 < Kb) (shift : Fin Kb) (count : ℕ) (cell : ℤ)
    (M C P : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) (hα : 1 ≤ α) (hp0 : 0 < p)
    (good : Set X) (hgood : MeasurableSet good) (bad : τ → Set X)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ x ∈ good, ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (hbad : ∀ x ∈ good, (1+C^p*(M+1)^(α-1))*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2)
    (hpathInt : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x)) μ)
    (hpathBound : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x) x ∂μ) ≤ P*∫ x, weight t x ∂μ) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
    let amp := fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell
    IntegrableOn (fun x => ‖(n x^(α/p-1)) • amp x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(α/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
        ((1+C^p*(M+1)^(α-1))*(1+2*P)*
          ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
            ∫ x, weight t x ∂μ)^(1/p) := by
  intro n amp
  have hvertex := g.source_packet_vertex_integral μ tops slope precision cutoff weight hp hw
    hwint hwmeas K gap packets assigned stop value hv phase a α p hKb shift count cell
    M C P hM hC hα hp0.le good hgood bad hne hterminal henvelope hbad hpathInt hpathBound
  let R := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell
  have hn : ∀ x, 0 < n x := by
    intro x
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw
      (ShiftedBlocks.endpoint shift 0) cell x ht
  have hnint : Integrable n μ := integrable_finsetSum R (fun t ht =>
    hwint t ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1)
  have hvi : Integrable (fun x => vertexAmount (n x) (amp x) α p) (μ.restrict good) :=
    (integrable_indicator_iff hgood).mp hvertex.1
  have hvb : (∫ x, vertexAmount (n x) (amp x) α p ∂μ.restrict good) ≤
      (1+C^p*(M+1)^(α-1))*(1+2*P)*∑ t ∈ R, ∫ x, weight t x ∂μ := by
    rw [← integral_indicator hgood]
    exact hvertex.2
  exact ⟨normalized_vertex_energy_integrable (μ.restrict good) n amp hn hp0.ne'
      hnint.restrict hvi,
    normalized_vertex_moment_le (μ.restrict good) n amp hn hp0 hnint.restrict hvi hvb⟩

end LipschitzHilbert.AngularGrid

end

end OAI
