import Mathlib.Tactic.Abel
import OAI.Computability.PerfectCompleteness.Algebra.TensorAffineHeavyWitness
import OAI.Computability.PerfectCompleteness.Decoding.DecoderContraction
import OAI.Computability.PerfectCompleteness.Machines.OwnInputHeavyBounds

namespace OAI


namespace PerfectCompleteness.RightDecoderWitness

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TensorCosetEvaluation
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

noncomputable section

section Algebra

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

theorem scalarRestriction_row_add (W : Submodule F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (u v : W) :
    scalarRestriction Φ (u + v) = scalarRestriction Φ u + scalarRestriction Φ v := by
  ext h
  simp only [scalarRestriction_apply, TensorProduct.add_tmul, map_add, LinearMap.add_apply]

theorem errorSpace_of_normalized_rows (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (z : Module.Dual F2 H)
    (hσ : σ.comp W.subtype ≠ 0)
    (hgood : ∀ w : W, σ w.val = 1 → scalarRestriction Φ w - z ∈ Q) :
    Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q := by
  intro w
  rw [scalarRestriction_sub]
  change scalarRestriction Φ w - scalarRestriction (pureFrequency (σ.comp W.subtype) z) w ∈ Q
  rw [scalarRestriction_pure]
  change scalarRestriction Φ w - σ w.val • z ∈ Q
  rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (σ w.val) with hzero | hone
  · rw [hzero, zero_smul, sub_zero]
    let w₀ := DecoderContraction.chosenRow W σ hσ
    have hw₀ : σ w₀.val = 1 := DecoderContraction.chosenRow_value_one W σ hσ
    have hsum : σ (w₀ + w).val = 1 := by
      simp only [Submodule.coe_add, map_add, hw₀, hzero, add_zero]
    have hdifference := Q.sub_mem (hgood (w₀ + w) hsum) (hgood w₀ hw₀)
    rw [scalarRestriction_row_add] at hdifference
    have heq : (scalarRestriction Φ w₀ + scalarRestriction Φ w - z) -
        (scalarRestriction Φ w₀ - z) = scalarRestriction Φ w := by
      abel
    rwa [heq] at hdifference
  · simpa only [hone, one_smul] using hgood w hone

end Algebra

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)
  (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a)

local instance upperSpaceFintype : Fintype (UpperSpace slots upper) := Fintype.ofFinite _

theorem heavyList_eq (threshold : ℝ) (σ : Module.Dual F2 (UpperVector rows upper)) :
    TensorAffineHeavyWitness.heavyList W
      (referenceLaw slots rows upper lower W repeats cut)
      (response slots rows upper lower W a labeling input) threshold σ =
      heavyList slots rows upper lower W a repeats cut labeling input σ threshold := by
  ext Φ
  simp only [TensorAffineHeavyWitness.heavyList, OwnLawHeavyList.mem_heavyList,
    OwnLawHeavyList.character, OwnInputReference.mem_heavyList]

def conditionalMatch
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper) : ℝ :=
  TensorAffineHeavyWitness.conditionalMatch W
    (referenceLaw slots rows upper lower W repeats cut)
    (response slots rows upper lower W a labeling input) Q target z offset

theorem exists_heavy_error_coset
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ conditionalMatch slots rows upper lower W a repeats cut labeling input
      Q target z offset) :
    ∃ σ : Module.Dual F2 (UpperVector rows upper), σ.comp W.subtype ≠ 0 ∧
      ∃ Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ (ρ * h₀ / 4),
        Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q := by
  have hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper), Φ ≠ 0 →
      |(referenceLaw slots rows upper lower W repeats cut).expectation
        (fun X => QuarterBalance.sign (Φ X))| ≤ (7 / 8 : ℝ) ^ repeats (Nodes.height upper) := by
    intro Φ hΦ
    apply OwnInputHeavyBounds.referenceLaw_sign_bias_le slots rows upper lower W repeats cut
      ((7 / 8 : ℝ) ^ repeats (Nodes.height upper)) ?_ Φ hΦ
    intro f hf
    exact RecursiveSamplerBias.law_bias_le_height repeats hrep cut.path
      (LeafDomain (nodeSlots slots upper)) f hf
  obtain ⟨σ, hσ, Φ, hΦ, hgood⟩ := TensorAffineHeavyWitness.exists_heavy_candidate W
    (referenceLaw slots rows upper lower W repeats cut)
    (response slots rows upper lower W a labeling input)
    ρ h₀ ((7 / 8 : ℝ) ^ repeats (Nodes.height upper)) hρ hh₀
    (pow_nonneg (by norm_num) _) hsmall hbias hexcluded Q hsize target z offset hmatch
  refine ⟨σ, hσ, Φ, ?_, errorSpace_of_normalized_rows W Q σ Φ z hσ hgood⟩
  rw [← heavyList_eq slots rows upper lower W a repeats cut labeling input]
  exact hΦ

theorem exists_contracted_candidate
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ conditionalMatch slots rows upper lower W a repeats cut labeling input
      Q target z offset) :
    ∃ σ : Module.Dual F2 (UpperVector rows upper), σ.comp W.subtype ≠ 0 ∧
      ∃ Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ (ρ * h₀ / 4),
        DecoderContraction.contract W σ Φ - z ∈ Q := by
  obtain ⟨σ, hσ, Φ, hΦ, herror⟩ := exists_heavy_error_coset slots rows upper lower W a
    repeats cut labeling input ρ h₀ hρ hh₀ hrep hsmall hexcluded Q hsize target z offset hmatch
  exact ⟨σ, hσ, Φ, hΦ, DecoderContraction.contract_sub_mem W Q σ Φ z hσ herror⟩

end
end PerfectCompleteness.RightDecoderWitness

end OAI
