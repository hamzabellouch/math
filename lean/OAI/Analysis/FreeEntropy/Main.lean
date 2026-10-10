import OAI.Analysis.FreeEntropy.CutoffSeparation

namespace OAI

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation

theorem main :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (M : VonNeumannAlgebra H) (τ : TracialVector M)
      (n : ℕ) (X S : Fin n → H →L[ℂ] H),
      2 ≤ n ∧
      (∀ i, X i ∈ M ∧ IsSelfAdjoint (X i)) ∧
      (∀ i, S i ∈ M ∧ IsSelfAdjoint (S i)) ∧
      FreeStandardNoise τ X S ∧
      (⊥ : EReal) < chi τ X ∧
      chi τ X ≤ chiStar τ X S - (1 / 2 : EReal) ∧
      chiStar τ X S - (1 / 2 : EReal) < (⊤ : EReal) := by
  obtain ⟨δ,Δ,hδ,hΔ,hδΔ,hsep,hq⟩ := exists_spectral_parameters chosenP_ge_two
  obtain ⟨h,hh0,hh1,hh⟩ := exists_small_h_spectralGood chosenP_ge_two hδ hΔ
  refine ⟨Model.H chosenP,inferInstance,inferInstance,inferInstance,Model.M chosenP,
    Model.τ chosenP,chosenP+1,Model.X chosenP h,Model.auxiliaryNoise chosenP,
    by have := chosenP_ge_two; omega,
    (fun i => ⟨Model.X_mem chosenP h i,Model.X_selfAdjoint chosenP h i⟩),
    (fun i => ⟨Model.auxiliaryNoise_mem chosenP i,Model.auxiliaryNoise_selfAdjoint chosenP i⟩),
    Model.auxiliaryNoise_free chosenP h,Model.chi_gt_bot chosenP chosenP_ge_two hh0,
    chosen_chi_bound hh0 hh1 hδ hΔ hδΔ hsep hq hh,?_⟩
  rw [Model.chiStar_tail_formula chosenP chosenP_ge_two h hh0]
  change ((Model.gaussianEntropy chosenP h-(1/2:ℝ)*(∫u in Set.Ioi h,Model.fisherDeficit chosenP u):ℝ):EReal)-(((1/2:ℝ):ℝ):EReal)<⊤
  rw [← EReal.coe_sub]
  exact EReal.coe_lt_top _

end FiniteEntropySeparation

end

end OAI
