import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongDyads
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailCounting

namespace OAI

/-! Summing the actual long-completion dyads with the counting estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem metaplectic_long_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein), primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (U B C F M : ℝ),
      0 < U → 0 ≤ B → 0 < C → B*U ≤ F → 0 ≤ M →
      (∀ x : ℝ, B < x → W x = 0) → (∀ x, ‖W x‖ ≤ M) →
      ‖metaplecticLongCompletion r ℓ W U C F‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_tail_dyad_counting hε hεsmall
  refine ⟨D,hD,?_⟩
  intro r hr ℓ W U B C F M hU hB hC hF hM hcut hW
  rw [metaplectic_long_completion_active r ℓ W hU hB hF hcut C,
    metaplectic_long_dyad_partition]
  have hb (j : ℕ) (hj : j ∈ metaplecticLongDyads C F) :
      ‖∑ e ∈ metaplecticLongDyad C F j, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε) := by
    have hCE : C/2 ≤ (2:ℝ)^j := by linarith [metaplecticLongDyad_cutoff hj]
    have hs := hbound r hr ℓ C F (metaplecticLongDyad C F j) ((2:ℝ)^j) U B M
      (by positivity) hU hB hM (fun e he => metaplecticLongDyad_norm he) W hcut hW
    apply hs.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hCE (by linarith)
  calc
    _ ≤ ∑ j ∈ metaplecticLongDyads C F, D*B*M*U*(C/2)^(-3/2+ε) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = _ := by simp; ring

theorem metaplectic_long_outer_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Finset Eisenstein) (α : Eisenstein → ℂ)
      (ℓ : ℤ) (W : Eisenstein → ℝ → ℂ) (U B C F M : ℝ),
      0 < U → 0 ≤ B → 0 < C → B*U ≤ F → 0 ≤ M →
      (∀ r ∈ A, primary r) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) →
      (∀ r ∈ A, ∀ x, ‖W r x‖ ≤ M) →
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W r) U C F‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card*(∑ r ∈ A, ‖α r‖) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_long_counting hε hεsmall
  refine ⟨D,hD,?_⟩
  intro A α ℓ W U B C F M hU hB hC hF hM hA hcut hW
  calc
    _ ≤ ∑ r ∈ A, ‖α r‖*‖metaplecticLongCompletion r ℓ (W r) U C F‖ := by
      simpa only [norm_mul] using norm_sum_le A (fun r => α r*metaplecticLongCompletion r ℓ (W r) U C F)
    _ ≤ ∑ r ∈ A, ‖α r‖*(D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
        (hbound r (hA r hr) ℓ (W r) U B C F M hU hB hC hF hM (hcut r hr) (hW r hr))
        (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
