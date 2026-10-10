import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.SourceDensityCompactEquation
import OAI.Analysis.RieszRectifiability.Rigidity.BoundedFractionalRigidity

namespace OAI

/-!
# Constant planar densities

An almost-everywhere constant density pushes forward under a linear isometry to a scalar multiple
of planar volume. The compact fractional equation and bounded-density rigidity identify this
constant for reflectionless weak limits, retaining its positive lower and finite upper bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem ae_constant_planar_density_measure {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient n → ℝ) (q : ℝ)
    (heq : ∀ᵐ x ∂volume, f x = q) :
    ((volume : Measure (Ambient n)).withDensity
      (fun x => ENNReal.ofReal (f x))).map L =
      ENNReal.ofReal q • (volume : Measure (Ambient n)).map L := by
  have hd : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume] fun _ => ENNReal.ofReal q :=
    heq.mono fun _ hx => congrArg ENNReal.ofReal hx
  rw [withDensity_congr_ae hd, withDensity_const,
    Measure.map_smul _ L.continuous.measurable.aemeasurable]

theorem source_planar_density_ae_constant {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (cMass * r ^ (p + 1)) ≤ ν (ball 0 r))
    (hreflect : ScalarReflectionlessAt (p + 1) ν 0) :
    ∃ q : ℝ, c ≤ q ∧ q ≤ M ∧ 0 < q ∧
      (∀ᵐ x ∂volume, f x = q) ∧
      ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map L := by
  obtain ⟨q, heq⟩ := bounded_density_ae_constant_of_compact_fractional_equation p f hf M hupper
    (source_planar_density_compact_fractional_equation p C G μ ν hgrowth hgν hweak D hB
      L f hf c hc hlower M hupper hdensity cMass hcMass hlowerMass hreflect)
  obtain ⟨x, hx⟩ := heq.exists
  have hcq : c ≤ q := hx ▸ hlower x
  have hqM : q ≤ M := hx ▸ (le_abs_self (f x)).trans (hupper x)
  exact ⟨q, hcq, hqM, hc.trans_le hcq, heq,
    hdensity.symm.trans (ae_constant_planar_density_measure L f q heq)⟩

end

end RieszRectifiability

end OAI
