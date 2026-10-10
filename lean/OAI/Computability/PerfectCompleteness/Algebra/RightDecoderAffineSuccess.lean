import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderLemmas
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderWitness
import OAI.Computability.PerfectCompleteness.Foundations.OutputAnnihilator

namespace OAI

section

namespace PerfectCompleteness.RightDecoderAffineSuccess

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)
  (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a)

attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

theorem character_count :
    Fintype.card (Module.Dual F2 (UpperVector rows upper)) =
      2 ^ rows (Nodes.height upper) := by
  simpa only [OwnInputReference.UpperVector, HierarchicalArrays.Block,
    Module.finrank_fin_fun] using
    (OutputAnnihilator.card_dual (K := UpperVector rows upper))

theorem coset_probability_lower
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρ * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ RightDecoderWitness.conditionalMatch slots rows upper lower W a
      repeats cut labeling input Q target z offset) :
    (ρ * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper)) ≤
      (RightDecoder.law slots rows upper lower W a repeats cut labeling input (ρ * h₀ / 4)).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  have hthreshold : 0 < ρ * h₀ / 4 := div_pos (mul_pos hρ hh₀) (by norm_num)
  obtain ⟨σ, hσ, Φ, hΦ, herror⟩ :=
    RightDecoderWitness.exists_heavy_error_coset slots rows upper lower W a
      repeats cut labeling input ρ h₀ hρ hh₀ hrep hslice hexcluded Q hsize target z offset hmatch
  have h := RightDecoder.coset_lower_of_balanced slots rows upper lower W a
    repeats cut labeling input (ρ * h₀ / 4) hrep hthreshold hlist Q z
    ⟨σ, Φ, hΦ, hσ, herror⟩
  simpa only [character_count rows upper, Nat.cast_pow, Nat.cast_ofNat] using h

theorem coset_probability_pos
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρ * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ RightDecoderWitness.conditionalMatch slots rows upper lower W a
      repeats cut labeling input Q target z offset) :
    0 < (RightDecoder.law slots rows upper lower W a repeats cut labeling input (ρ * h₀ / 4)).probability
      (fun decoded => decide (decoded - z ∈ Q)) := by
  have hthreshold : 0 < ρ * h₀ / 4 := div_pos (mul_pos hρ hh₀) (by norm_num)
  have hfactor : 0 < (ρ * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper)) :=
    div_pos (pow_pos hthreshold _) (mul_pos (by norm_num) (pow_pos (by norm_num) _))
  exact hfactor.trans_le (coset_probability_lower slots rows upper lower W a repeats cut
    labeling input ρ h₀ hρ hh₀ hrep hslice hlist hexcluded Q hsize target z offset hmatch)

end
end PerfectCompleteness.RightDecoderAffineSuccess

end

end OAI
