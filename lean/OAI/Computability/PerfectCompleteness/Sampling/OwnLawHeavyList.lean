import OAI.Computability.PerfectCompleteness.Construction.OwnBucketBias

namespace OAI

section

namespace PerfectCompleteness.OwnLawHeavyList

open QuarterBalance
open HiddenBucketBias (recursiveLaw)
open UniqueGamesTheorem.Foundations.Games
open scoped TensorProduct Classical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]

local instance dualFintype : Fintype (Module.Dual F2 V) :=
  Fintype.ofInjective (fun f : Module.Dual F2 V => (f : V → F2)) DFunLike.coe_injective

def character (f : Module.Dual F2 V) (x : V) : ℝ := sign (f x)

omit [Fintype V] in
theorem character_sq (f : Module.Dual F2 V) (x : V) : character f x ^ 2 = 1 := by
  unfold character sign
  split <;> norm_num

omit [Fintype V] in
theorem character_pair (f g : Module.Dual F2 V) (x : V) :
    character f x * character g x = character (f - g) x := by
  simp only [character, sub_eq_add_neg,
    LinearMap.add_apply, LinearMap.neg_apply, ZMod.neg_eq_self_mod_two, sign_add]

def heavyList (μ : FiniteDistribution V) (target : V → ℝ) (threshold : ℝ) :
    Finset (Module.Dual F2 V) :=
  SmallBias.heavySet μ character target threshold

theorem mem_heavyList (μ : FiniteDistribution V) (target : V → ℝ) (threshold : ℝ)
    (f : Module.Dual F2 V) :
    f ∈ heavyList μ target threshold ↔
      threshold ≤ |μ.expectation (fun x => target x * character f x)| := by
  simp only [heavyList, SmallBias.heavySet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem heavyList_card_le (μ : FiniteDistribution V) (target : V → ℝ)
    (threshold bias : ℝ) (hthreshold : 0 < threshold) (hbias : 0 ≤ bias)
    (hsmall : bias ≤ threshold ^ 2 / 2) (htarget : ∀ x, target x ^ 2 ≤ 1)
    (hdual : ∀ f : Module.Dual F2 V, f ≠ 0 →
      |μ.expectation (fun x => sign (f x))| ≤ bias) :
    ((heavyList μ target threshold).card : ℝ) ≤ 2 / threshold ^ 2 := by
  apply SmallBias.heavySet_card_le μ character target threshold bias
    hthreshold hbias hsmall htarget (fun f x => (character_sq f x).le)
  intro f g hfg
  simp only [character_pair]
  exact hdual (f - g) (sub_ne_zero.mpr hfg)

universe u
variable {branch : Nat → Nat} {n m width : Nat}

theorem own_heavyList_card_le (W : Submodule F2 (Fin width → F2))
    (repeats : Nat → Nat) (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (p : DescendantSpaces.Path branch n m)
    (A : RecursiveSpaces.Slots branch n → Type u) [∀ s, Finite (A s)]
    (target : (W ⊗[F2] RecursiveSpaces.space F2 branch n A) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hsmall : (7 / 8 : ℝ) ^ repeats n ≤ threshold ^ 2 / 2)
    (htarget : ∀ x, target x ^ 2 ≤ 1) :
    ((heavyList (recursiveLaw W repeats p A) target threshold).card : ℝ) ≤
      2 / threshold ^ 2 := by
  let : Fintype (RecursiveSpaces.space F2 branch n A) := Fintype.ofFinite _
  apply heavyList_card_le (recursiveLaw W repeats p A) target threshold
    ((7 / 8 : ℝ) ^ repeats n) hthreshold (pow_nonneg (by norm_num) _) hsmall htarget
  exact fun f hf => OwnBucketBias.bias_le W repeats hrep p A f hf

end
end PerfectCompleteness.OwnLawHeavyList

end

end OAI
