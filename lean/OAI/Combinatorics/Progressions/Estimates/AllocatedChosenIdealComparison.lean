import OAI.Combinatorics.Progressions.Linear.AllocatedGoodKernelIdealComparison
import OAI.Combinatorics.Progressions.Polynomial.AllocatedIdealScalePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uGeom uCover

open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_chosen_ideal_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D E p₀ : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hE : 0 ≤ E) (hp₀ : 0 ≤ p₀) :
    let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
    let ε : ℝ := physicalIdealErrorShare E (D * w)
    let e : ℝ := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
      (α := α) hLayer A T E (D * w)
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧
      let t : ℝ := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      AllocatedChosenIdealAt.{uGeom, uCover, _, _, _, _, _}
        (G := G) (α := α) (O := O) B D E p₀ e δ t := by
  dsimp only
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hp₀
  have hDw : 0 ≤ D * w := mul_nonneg hdim.nonneg hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer A T E (D * w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T hE hDw
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ :=
    exists_allocated_goodKernel_ideal_comparison (G := G) (α := α) (O := O)
      B ψ hψ hrange hzero hone A T hLip hTransition hdim hE hp₀
  exact ⟨δ, hδ, hδ1, hδeq, ht, ht1,
    allocatedGoodKernelIdealAt_chooseScale B hdim hE hp₀ he hcompare⟩

end Erdos3.VectorPolynomial

end

end OAI
