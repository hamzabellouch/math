import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatentSupportLemmas

namespace OAI

section

namespace PerfectCompleteness.OwnInputHeavyBounds

open scoped TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

noncomputable section

theorem sign_sq (b : F2) : QuarterBalance.sign b ^ 2 = 1 := by
  by_cases hb : b = 0 <;> simp [QuarterBalance.sign, hb]

theorem frequency_add_ne_zero {V : Type*} [AddCommGroup V] [Module F2 V]
    (Φ Ψ : Module.Dual F2 V) (hne : Φ ≠ Ψ) : Φ + Ψ ≠ 0 := by
  intro hzero
  apply hne
  ext X
  have hsum : Φ X + Ψ X = 0 := by
    simpa only [LinearMap.add_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun hzero X
  exact add_right_cancel (hsum.trans (CharTwo.add_self_eq_zero (Ψ X)).symm)

theorem character_mul {V : Type*} [AddCommGroup V] [Module F2 V]
    (Φ Ψ : Module.Dual F2 V) (X : V) :
    QuarterBalance.sign (Φ X) * QuarterBalance.sign (Ψ X) =
      QuarterBalance.sign ((Φ + Ψ) X) :=
  (QuarterBalance.sign_add (Φ X) (Ψ X)).symm

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

local instance upperSpaceFintype : Fintype (UpperSpace slots upper) :=
  Fintype.ofFinite _

theorem referenceLaw_sign_bias_le (repeats : Nat → Nat) (cut : Cut upper lower)
    (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 (UpperSpace slots upper), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats cut.path (LeafDomain (nodeSlots slots upper))).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) (hΦ : Φ ≠ 0) :
    |(referenceLaw slots rows upper lower W repeats cut).expectation
      (fun X => QuarterBalance.sign (Φ X))| ≤ bound :=
  HiddenBucketBias.recursive_law_sign_bias_le W repeats cut.path
    (LeafDomain (nodeSlots slots upper)) bound scalar_bias Φ hΦ

theorem referenceLaw_pair_bias_le (repeats : Nat → Nat) (cut : Cut upper lower)
    (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 (UpperSpace slots upper), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats cut.path (LeafDomain (nodeSlots slots upper))).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound)
    (Φ Ψ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) (hne : Φ ≠ Ψ) :
    |(referenceLaw slots rows upper lower W repeats cut).expectation
      (fun X => QuarterBalance.sign (Φ X) * QuarterBalance.sign (Ψ X))| ≤ bound := by
  simp_rw [← QuarterBalance.sign_add]
  exact referenceLaw_sign_bias_le slots rows upper lower W repeats cut bound
    scalar_bias (Φ + Ψ)
    (frequency_add_ne_zero (V := W ⊗[F2] UpperSpace slots upper) Φ Ψ hne)

theorem heavyList_card_le (a : LowerVector rows lower)
    (repeats : Nat → Nat) (cut : Cut upper lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold bound : ℝ)
    (hthreshold : 0 < threshold) (hbound : 0 ≤ bound)
    (hsmall : bound ≤ threshold ^ 2 / 2)
    (scalar_bias : ∀ f : Module.Dual F2 (UpperSpace slots upper), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats cut.path (LeafDomain (nodeSlots slots upper))).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound) :
    ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤
      2 / threshold ^ 2 := by
  let μ : UniqueGamesTheorem.Foundations.Games.FiniteDistribution
      (W ⊗[F2] UpperSpace slots upper) :=
    referenceLaw slots rows upper lower W repeats cut
  let chars : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper) →
      (W ⊗[F2] UpperSpace slots upper) → ℝ :=
    fun Φ X => QuarterBalance.sign (Φ X)
  let target : (W ⊗[F2] UpperSpace slots upper) → ℝ :=
    fun X => QuarterBalance.sign (σ (response slots rows upper lower W a labeling input X))
  have htarget : ∀ X, target X ^ 2 ≤ 1 := by
    intro X
    exact (sign_sq _).le
  have hchars : ∀ Φ X, chars Φ X ^ 2 ≤ 1 := by
    intro Φ X
    exact (sign_sq _).le
  have hpair : ∀ Φ Ψ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper), Φ ≠ Ψ →
      |μ.expectation (fun X => chars Φ X * chars Ψ X)| ≤ bound := by
    intro Φ Ψ hne
    exact referenceLaw_pair_bias_le slots rows upper lower W repeats cut bound
      scalar_bias Φ Ψ hne
  exact SmallBias.heavySet_card_le
    (Ω := W ⊗[F2] UpperSpace slots upper)
    (I := Module.Dual F2 (W ⊗[F2] UpperSpace slots upper))
    μ chars target threshold bound hthreshold hbound hsmall htarget hchars hpair

theorem heavyList_card_le_of_balanced (a : LowerVector rows lower)
    (repeats : Nat → Nat) (cut : Cut upper lower)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold : ℝ)
    (hthreshold : 0 < threshold)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ threshold ^ 2 / 2) :
    ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤
      2 / threshold ^ 2 := by
  have scalar_bias : ∀ f : Module.Dual F2 (UpperSpace slots upper), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats cut.path (LeafDomain (nodeSlots slots upper))).expectation
        (fun h => QuarterBalance.sign (f h))| ≤
          (7 / 8 : ℝ) ^ repeats (Nodes.height upper) := by
    intro f hf
    exact RecursiveSamplerBias.law_bias_le_height
      (branch := branch) (n := Nodes.height upper) (m := Nodes.height lower)
      repeats hrep cut.path (LeafDomain (nodeSlots slots upper)) f hf
  exact heavyList_card_le slots rows upper lower W a repeats cut labeling input σ
    threshold ((7 / 8 : ℝ) ^ repeats (Nodes.height upper)) hthreshold
    (pow_nonneg (by norm_num) _) hsmall scalar_bias

end

end PerfectCompleteness.OwnInputHeavyBounds

end

end OAI
