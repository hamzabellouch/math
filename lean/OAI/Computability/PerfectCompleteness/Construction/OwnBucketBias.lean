import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatentSupportLemmas

namespace OAI

section

namespace PerfectCompleteness.OwnBucketBias

open RecursiveSpaces DescendantSpaces HiddenBucketBias
open UniqueGamesTheorem.Foundations.Games
open scoped TensorProduct

noncomputable section

universe u
variable {branch : Nat → Nat} {n m width : Nat}

theorem bias_le (W : Submodule F2 (Fin width → F2))
    (repeats : Nat → Nat) (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n A)]
    (Φ : Module.Dual F2 (W ⊗[F2] space F2 branch n A)) (hΦ : Φ ≠ 0) :
    |(recursiveLaw W repeats p A).expectation (fun x => QuarterBalance.sign (Φ x))| ≤
      (7 / 8 : ℝ) ^ repeats n := by
  apply recursive_law_sign_bias_le W repeats p A _ ?_ Φ hΦ
  intro f hf
  exact RecursiveSamplerBias.law_bias_le_height repeats hrep p A f hf

theorem bias_le_of_six_le (W : Submodule F2 (Fin width → F2))
    (repeats : Nat → Nat) (hrep : ∀ k, 6 ≤ repeats (k + 1))
    (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n A)]
    (Φ : Module.Dual F2 (W ⊗[F2] space F2 branch n A)) (hΦ : Φ ≠ 0) :
    |(recursiveLaw W repeats p A).expectation (fun x => QuarterBalance.sign (Φ x))| ≤
      (7 / 8 : ℝ) ^ repeats n :=
  bias_le W repeats (RecursiveSamplerBias.repetitionsBalanced_of_six_le repeats hrep) p A Φ hΦ

theorem mixed_bias_le {t : Nat} (W : Submodule F2 (Fin width → F2))
    (repeats : Nat → Nat) (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (Φ : Module.Dual F2 (W ⊗[F2] TreeSourceSpaces.H slots)) (hΦ : Φ ≠ 0) :
    |(recursiveLaw W repeats p (TreeSourceSpaces.LeafDomain slots)).expectation
        (fun x => QuarterBalance.sign (Φ x))| ≤ (7 / 8 : ℝ) ^ repeats n := by
  let : Fintype (TreeSourceSpaces.H slots) := Fintype.ofFinite _
  exact bias_le W repeats hrep p (TreeSourceSpaces.LeafDomain slots) Φ hΦ

end
end PerfectCompleteness.OwnBucketBias

end

end OAI
