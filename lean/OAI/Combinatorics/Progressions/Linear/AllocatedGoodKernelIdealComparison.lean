import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealComparisonAssembly

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uCover uGeom

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_goodKernel_ideal_comparison
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
      AllocatedGoodKernelIdealAt.{uCover, _, _, _, _, _, uGeom}
        (G := G) (α := α) (O := O) B D E p₀ e δ t := by
  dsimp only
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hp₀
  have hDw : 0 ≤ D * w := mul_nonneg hdim.nonneg hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
    (α := α) hLayer A T E (D * w)
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg hLayer A T hE hDw
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ :=
    exists_allocated_physical_ideal_comparison.{_, _, _, _, _, uGeom, uCover}
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition
    (physicalIdealErrorShare_pos E (D * w))
  have hδe : (δ : ℝ)⁻¹ ≤ Real.exp e := by
    rw [hδeq]
    exact physicalIdeal_smoothing_inverse_le_exp hLayer (fun _ => Nat.succ_pos _)
      A T hE hDw
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  exact allocated_goodKernel_ideal_of_comparison B hdim hE hp₀ he hδe ht1 hcompare

end Erdos3.VectorPolynomial

end

end OAI
