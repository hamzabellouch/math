import OAI.Geometry.SurfaceImmersion.Correction.PolynomialRootBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! Polynomial bounds for the supported square-root amplitudes of the
metric decomposition, including their difference estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def phaseAmplitudeBudget (m : ℕ) (D B : ℝ) : ℝ :=
  1+2^m*B*sqrtBudget m D B+2^m*B*rootDifferenceBudget m D B

theorem polynomial_phaseAmplitude_bounds (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U : Set E}, UniqueDiffOn ℝ U → ∀ {s B A : ℝ} {ψ f g : E → ℝ},
      0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B ψ → WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ f) ∧
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ g) ∧
      WeightedBound U s m (C*B^d*A) (fun x => phaseAmplitude ψ f x-phaseAmplitude ψ g x) := by
  obtain ⟨D,hD,hr⟩ := polynomial_root_bounds (E := E) m
  have hpoly : HasPolynomialBound (phaseAmplitudeBudget m D) := by
    unfold phaseAmplitudeBudget rootDifferenceBudget sqrtBudget
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro U hU s B A ψ f g hs hB hA hψ hf hg hfp hgp hfi hgi hbψ hbf hbg hdiff
  obtain ⟨bF,bG,bDiff⟩ := hr hU hs hB hA hf hg hfp hgp hfi hgi hbf hbg hdiff
  have hB0 := zero_le_one.trans hB
  have hS := sqrtBudget_nonneg m (zero_le_one.trans hD) hB0
  have hR : 0 ≤ rootDifferenceBudget m D B := by unfold rootDifferenceBudget; positivity
  have hleft : 2^m*B*sqrtBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*rootDifferenceBudget m D B := by positivity
    linarith
  have hright : 2^m*B*rootDifferenceBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*sqrtBudget m D B := by positivity
    linarith
  have hfroot := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hgroot := hg.sqrt (fun x hx => (hgp x hx).ne')
  have hfa := hbψ.mul_real hU hs.le hB0 hS hψ hfroot bF
  have hga := hbψ.mul_real hU hs.le hB0 hS hψ hgroot bG
  refine ⟨hfa.mono_const (hleft.trans (hpoly B hB).2),
    hga.mono_const (hleft.trans (hpoly B hB).2),?_⟩
  have hda := hbψ.mul_real hU hs.le hB0 (mul_nonneg hR hA) hψ (hfroot.sub hgroot) bDiff
  have hsize : 2^m*B*(rootDifferenceBudget m D B*A) ≤ C*B^d*A := by
    calc
      _ = (2^m*B*rootDifferenceBudget m D B)*A := by ring
      _ ≤ C*B^d*A := mul_le_mul_of_nonneg_right (hright.trans (hpoly B hB).2) hA
  apply (hda.mono_const hsize).congr
  intro x hx
  dsimp only [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

end

end OAI
