import Mathlib
import OAI.Computability.DirectedFeedback.Games.TensorDomination

namespace OAI


section

namespace DFVSGames.Explicit.BipartiteGame

open DFVSGames.Foundations.Games

noncomputable section

variable {L R E A : Type*}
  [Fintype L] [Fintype R] [Fintype E] [Fintype A]
  [Nonempty E] [Nonempty A]

theorem product_soundness_rate (G : BipartiteGame L R E A) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [product_value_eq_repetition]
  exact DFVSGames.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem product_soundness (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ δ :=
  (G.product_soundness_rate t hvalue).trans hcount

theorem product_explicit_soundness [DecidableEq A]
    (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).value ≤ δ := by
  classical
  rw [← toGame_value]
  exact G.product_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

noncomputable section

variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E] [Nonempty E]

theorem binaryProduct_soundness_rate {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [binaryProduct_value_eq_repetition]
  exact DFVSGames.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem binaryProduct_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ δ :=
  (G.binaryProduct_soundness_rate t hvalue).trans hcount

theorem binaryProduct_explicit_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).value ≤ δ := by
  rw [← toGame_value]
  exact G.binaryProduct_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

end DFVSGames.Explicit.BipartiteGame

namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply DFVSGames.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end DFVSGames.Explicit.ProductPaddedOutput
end


namespace DFVSGames.FinishReduction

open DFVSGames.Foundations Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Integration
open Explicit

noncomputable section

def of_matrix_reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    {q s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (matrix : List Bool → Instance q)
    (translations : ∀ input, TranslationTarget.IsTranslationInstance coordinates (matrix input))
    (computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      gameBits matrix)
    (finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm)
    (d : ℚ) (hd : d ≤ P.epsilon0 / P.repetitions)
    (complete : ∀ input, BinaryLanguage.language input →
      1 - (d : ℝ) ≤ InstanceValue.value (matrix input))
    (sound : ∀ input, ¬BinaryLanguage.language input →
      InstanceValue.value (matrix input) ≤ 99 / 100) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hqpos : 0 < q := by omega
  have hC : 0 < P.copies := by have h := P.copies_large; omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let rounded := fun input => UniformTarget.construct P.copies hC (matrix input)
  have roundedTranslations : ∀ input,
      TranslationTarget.IsTranslationInstance coordinates (rounded input) := fun input =>
    UniformTarget.translations P.copies hC (matrix input) coordinates (translations input)
  let roundedMachine := MachineSequential.composeBits
    (f := matrix) (g := UniformTarget.construct P.copies hC) computation
    (MachineUniformRun.computation (q := q) P.copies hC)
  have roundedFinite : MachineFiniteAlphabet.FiniteAlphabet roundedMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := matrix) (g := UniformTarget.construct P.copies hC) computation
      (MachineUniformRun.computation (q := q) P.copies hC) finiteAlphabet
      (MachineUniformRun.finiteAlphabet (q := q) P.copies hC)
  let base := fun input => SubdivisionTarget.subdivide (rounded input)
  let basePresentation := fun input => SubdivisionTarget.simpleBipartite (rounded input)
  let baseMachine := MachineSubdivisionCompose.translationComputableInPolyTime
    coordinates roundedMachine roundedTranslations
  have baseFinite : MachineFiniteAlphabet.FiniteAlphabet baseMachine.tm :=
    MachineSubdivisionCompose.finiteAlphabet roundedMachine
      (fun input => MachineSubdivisionCorrespondence.translations_involutive
        coordinates (rounded input) (roundedTranslations input)) roundedFinite
  let output := fun input => ProductPaddedOutput.output (base input)
    (basePresentation input) P.repetitions P.repetitions_pos
  let outputMachine := MachineProductRuntime.compose baseMachine basePresentation
    P.repetitions P.repetitions_pos
  have hqout : 2 ≤ q ^ P.repetitions :=
    hq.trans (Nat.le_self_pow P.repetitions_pos.ne' q)
  have hqoutpos : 0 < q ^ P.repetitions := by omega
  have baseValue (input : List Bool) :
      InstanceValue.value (base input) =
        1 - (1 - InstanceValue.value (matrix input)) / 4 := by
    dsimp [base, rounded]
    rw [SubdivisionTarget.value_eq _ hqpos,
      UniformTarget.value P.copies hC (matrix input) hqpos]
  have hτ : (0 : ℝ) < (P.pStar : ℝ) := by exact_mod_cast P.pStar_pos
  have hτsmall : (P.pStar : ℝ) ≤ 1 / 200 := by
    simpa only [ParameterSelection.OuterParameters.pStar, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one]
      using ((Rat.cast_le (K := ℝ)).mpr P.reciprocal_small)
  have hτbudget : (P.pStar : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast P.reciprocal_budget
  have hdbudget : (d : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast hd
  have hε0 : (0 : ℝ) ≤ (P.epsilon0 : ℝ) := by
    exact_mod_cast P.epsilon0_pos.le
  have roundingError (input : List Bool) :
      |InstanceValue.value (base input) -
        (1 - (1 - InstanceValue.value (matrix input)) / 4)| ≤ (P.pStar : ℝ) / 4 := by
    rw [baseValue input, sub_self, abs_zero]
    positivity
  refine {
    alphabet := q ^ P.repetitions
    alphabetAtLeastTwo := hqout
    dimension := s * P.repetitions
    dimensionPositive := by
      have hpos := Nat.mul_pos (show 0 < s by omega) P.repetitions_pos
      omega
    coordinates := ProductPaddedOutput.finalCoordinates coordinates P.repetitions
    construct := output
    simpleBipartite := fun input => ProductPaddedOutput.simpleBipartite
      (base input) (basePresentation input) P.repetitions P.repetitions_pos
    translations := fun input => ProductPaddedOutput.output_translations
      (base input) (basePresentation input) coordinates
      (SubdivisionTarget.subdivide_translation coordinates (rounded input)
        (roundedTranslations input)) P.repetitions P.repetitions_pos
    computation := outputMachine
    finiteAlphabet := MachineProductRuntime.compose_finiteAlphabet
      baseMachine basePresentation P.repetitions P.repetitions_pos baseFinite
    completeness := ?_
    soundness := ?_
  }
  · intro input yes
    apply (InstanceValue.exists_rate_ge_iff (output input) hqoutpos (1 - ε)).mpr
    have hbase := FinishBounds.subdivision_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (complete input yes) (roundingError input)
    have hproduct := ProductPaddedOutput.output_completeness (base input)
      (basePresentation input) P.repetitions P.repetitions_pos
      (error := 1 - InstanceValue.value (base input)) (by linarith)
    exact FinishBounds.final_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (P.epsilon0 : ℝ) ε P.repetitions P.repetitions_pos hbase hproduct
      hdbudget hτbudget hε0 P.epsilon0_le
  · intro input no
    apply (InstanceValue.forall_rate_le_iff (output input) hqoutpos δ).mpr
    have hbase := FinishBounds.subdivision_soundness _ _ (P.pStar : ℝ)
      (sound input no) hτsmall (roundingError input)
    exact (ProductPaddedOutput.output_soundness (base input) (basePresentation input)
      P.repetitions P.repetitions_pos P.soundness_rate hbase).trans P.delta0_le

end
end DFVSGames.FinishReduction


namespace DFVSGames.Decoder.SparseLaw

open scoped BigOperators
open DFVSGames.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

def uniformWeights (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => 1 / Fintype.card α

theorem uniformWeights_pos [Nonempty α] (a : α) : 0 < uniformWeights α a := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniformWeights_isProbability [Nonempty α] :
    IsProbability (uniformWeights α) := by
  constructor
  · exact fun a => (uniformWeights_pos a).le
  · simp [uniformWeights, Fintype.card_ne_zero]

def uniformChiSquare (p : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ) * ∑ a, (p a - uniformWeights α a) ^ 2

theorem uniformChiSquare_eq_pearson [Nonempty α] (p : α → ℝ) :
    uniformChiSquare p =
      ∑ a, uniformWeights α a * (p a / uniformWeights α a - 1) ^ 2 := by
  rw [uniformChiSquare, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformWeights]
  field_simp [hn]

theorem uniformChiSquare_eq_secondMoment [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) :
    uniformChiSquare p = (Fintype.card α : ℝ) * (∑ a, p a ^ 2) - 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint (a : α) :
      (Fintype.card α : ℝ) * (p a - uniformWeights α a) ^ 2 =
        (Fintype.card α : ℝ) * p a ^ 2 - 2 * p a + uniformWeights α a := by
    simp only [uniformWeights]
    field_simp [hn]
    ring
  rw [uniformChiSquare, Finset.mul_sum]
  simp only [hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2,
    (uniformWeights_isProbability (α := α)).2]
  ring

theorem uniformChiSquare_nonneg (p : α → ℝ) : 0 ≤ uniformChiSquare p := by
  unfold uniformChiSquare
  positivity

def mixture (β : ℝ) (p : α → ℝ) : α → ℝ :=
  fun a => (1 - β) * uniformWeights α a + β * p a

theorem mixture_isProbability [Nonempty α] (p : α → ℝ) (hp : IsProbability p)
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) : IsProbability (mixture β p) := by
  constructor
  · intro a
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos a).le)
      (mul_nonneg hβ (hp.1 a))
  · simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2,
      (uniformWeights_isProbability (α := α)).2]
    ring

theorem uniformChiSquare_mixture (p : α → ℝ) (β : ℝ) :
    uniformChiSquare (mixture β p) = β ^ 2 * uniformChiSquare p := by
  have hpoint (a : α) :
      (mixture β p a - uniformWeights α a) ^ 2 =
        β ^ 2 * (p a - uniformWeights α a) ^ 2 := by
    unfold mixture
    ring
  simp only [uniformChiSquare, hpoint, ← Finset.mul_sum]
  ring

theorem totalVariation_le_half_sqrt (p : α → ℝ) :
    totalVariation p (uniformWeights α) ≤ Real.sqrt (uniformChiSquare p) / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun _ => (1 : ℝ)) (fun a => |p a - uniformWeights α a|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  have hs := Real.le_sqrt_of_sq_le hcs
  exact div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)

def independentWeights (p : α → ℝ) (k : ℕ) : (Fin k → α) → ℝ :=
  fun x => ∏ i, p (x i)

theorem independentWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (k : ℕ) : IsProbability (independentWeights p k) := by
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => hp.1 (x i)
  · change (∑ x : Fin k → α, ∏ i, p (x i)) = 1
    rw [← Fintype.sum_pow, hp.2, one_pow]

theorem uniformChiSquare_independent [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) (k : ℕ) :
    uniformChiSquare (independentWeights p k) = (1 + uniformChiSquare p) ^ k - 1 := by
  rw [uniformChiSquare_eq_secondMoment _ (independentWeights_isProbability p hp k),
    uniformChiSquare_eq_secondMoment p hp]
  have hsecond : (∑ x : Fin k → α, independentWeights p k x ^ 2) =
      (∑ a, p a ^ 2) ^ k := by
    simp only [independentWeights, ← Finset.prod_pow]
    exact (Fintype.sum_pow (fun a => p a ^ 2) k).symm
  rw [hsecond]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← mul_pow]
  exact congrArg (fun t : ℝ => t ^ k - 1) (by ring)

theorem pow_mul_one_sub_le_one (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k * (1 - k * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + x) ^ k := pow_nonneg (by linarith) _
    have herr : 0 ≤ (1 + x) ^ k * ((k : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (mul_nonneg hp (by positivity)) (sq_nonneg x)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_fraction (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x < 1) :
    (1 + x) ^ k - 1 ≤ (k : ℝ) * x / (1 - (k : ℝ) * x) := by
  apply (le_div_iff₀ (sub_pos.mpr hk)).2
  have h := pow_mul_one_sub_le_one x hx k
  nlinarith

theorem pow_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k - 1 ≤ 2 * (k : ℝ) * x := by
  have hk' : (k : ℝ) * x < 1 := by linarith
  refine (pow_sub_one_le_fraction x hx k hk').trans ?_
  apply (div_le_iff₀ (sub_pos.mpr hk')).2
  have hn : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

def lineCount (z : V × V) : ℝ :=
  (if z.2 = 0 then 1 else 0) + (if z.1 = 0 then 1 else 0) +
    (if z.1 = z.2 then 1 else 0)

def singletonPairWeights (z : V × V) : ℝ := lineCount V z / (3 * Fintype.card V)

def singletonSamplerWeights (z : V × V) : ℝ :=
  ((∑ a : V, if (a, 0) = z then uniformWeights V a else 0) +
    (∑ a : V, if (0, a) = z then uniformWeights V a else 0) +
    (∑ a : V, if (a, a) = z then uniformWeights V a else 0)) / 3

theorem singletonSamplerWeights_eq (z : V × V) :
    singletonSamplerWeights V z = singletonPairWeights V z := by
  classical
  rcases z with ⟨x, y⟩
  have hleft : (∑ a : V, if (a, 0) = (x, y) then uniformWeights V a else 0) =
      if y = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hy : y = 0
    · simp [hy, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hy, hy]
  have hright : (∑ a : V, if (0, a) = (x, y) then uniformWeights V a else 0) =
      if x = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hx : x = 0
    · simp [hx, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hx, hx]
  have hdiag : (∑ a : V, if (a, a) = (x, y) then uniformWeights V a else 0) =
      if x = y then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hxy : x = y
    · simp [hxy, uniformWeights]
    · have hnone (a : V) : (a, a) ≠ (x, y) := by
        intro ha
        have he := Prod.mk.inj ha
        exact hxy (he.1.symm.trans he.2)
      simp [hnone, hxy]
  simp only [singletonSamplerWeights, hleft, hright, hdiag,
    singletonPairWeights, lineCount]
  split_ifs <;> ring

theorem lineCount_sum : ∑ z : V × V, lineCount V z = 3 * Fintype.card V := by
  have h₁ : (∑ z : V × V, if z.2 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  have h₂ : (∑ z : V × V, if z.1 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  have h₃ : (∑ z : V × V, if z.1 = z.2 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [lineCount, Finset.sum_add_distrib, h₁, h₂, h₃]
  ring

omit [Fintype V] in
theorem lineCount_sq (z : V × V) :
    lineCount V z ^ 2 = lineCount V z + (if z.1 = 0 ∧ z.2 = 0 then 6 else 0) := by
  by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;>
    by_cases hxy : z.1 = z.2 <;> simp_all [lineCount] ; norm_num

theorem lineCount_sq_sum :
    ∑ z : V × V, lineCount V z ^ 2 = 3 * Fintype.card V + 6 := by
  simp only [lineCount_sq, Finset.sum_add_distrib, lineCount_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : V)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem singletonPairWeights_isProbability : IsProbability (singletonPairWeights V) := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · intro z
    unfold singletonPairWeights lineCount
    positivity
  · simp only [singletonPairWeights, div_eq_mul_inv, ← Finset.sum_mul, lineCount_sum]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos (by norm_num) hn))

theorem singletonPairWeights_secondMoment :
    ∑ z : V × V, singletonPairWeights V z ^ 2 =
      (3 * Fintype.card V + 6) / (3 * Fintype.card V) ^ 2 := by
  simp only [singletonPairWeights, div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, lineCount_sq_sum]

theorem singletonPairWeights_chiSquare :
    uniformChiSquare (singletonPairWeights V) = ((Fintype.card V : ℝ) - 1) / 3 := by
  rw [uniformChiSquare_eq_secondMoment _ (singletonPairWeights_isProbability V),
    singletonPairWeights_secondMoment]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]
  ring

theorem paddedSlope_chiSquare (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    uniformChiSquare (independentWeights (mixture β (singletonPairWeights V)) k) =
      (1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1 := by
  rw [uniformChiSquare_independent _
    (mixture_isProbability _ (singletonPairWeights_isProbability V) hβ hβ'),
    uniformChiSquare_mixture, singletonPairWeights_chiSquare]
  exact congrArg (fun t : ℝ => (1 + t) ^ k - 1) (by ring)

theorem paddedSlope_totalVariation (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  simpa only [paddedSlope_chiSquare V β hβ hβ' k] using
    totalVariation_le_half_sqrt (independentWeights (mixture β (singletonPairWeights V)) k)

theorem paddedSlope_totalVariation_small (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (k : ℕ)
    (hk : (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt (2 * (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3)) / 2 := by
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card V))
  refine (paddedSlope_totalVariation V β hβ hβ' k).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact pow_sub_one_le_twice _ (by positivity) _ hk

theorem cubeSlope_totalVariation (m : ℕ) (hm : 0 < m)
    (hsize : 2 * ((Fintype.card V : ℝ) - 1) / 3 ≤ m) :
    totalVariation
      (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
      (uniformWeights (Fin (m ^ 3) → V × V)) ≤
        Real.sqrt (2 * ((Fintype.card V : ℝ) - 1) / (3 * m)) / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hbeta : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hmpos)).2
    nlinarith
  have hproduct : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) =
        ((Fintype.card V : ℝ) - 1) / (3 * m) := by
    push_cast
    field_simp [hmpos.ne']

  have hsmall : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2 := by
    rw [hproduct]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmpos)).2
    linarith
  have h := paddedSlope_totalVariation_small V (1 / (m : ℝ) ^ 2)
    (by positivity) hbeta (m ^ 3) hsmall
  convert h using 1
  congr 2
  calc
    2 * ((Fintype.card V : ℝ) - 1) / (3 * m) =
        2 * (((Fintype.card V : ℝ) - 1) / (3 * m)) := by ring
    _ = _ := by rw [← hproduct]; ring

theorem exists_cubeSlope_totalVariation_le (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ η := by
  obtain ⟨m, hm⟩ := exists_nat_ge
    (max (max (1 : ℝ) N)
      (max (2 * ((Fintype.card V : ℝ) - 1) / 3)
        (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2))))
  have hlow : max (1 : ℝ) N ≤ m := (le_max_left _ _).trans hm
  have hmone : (1 : ℝ) ≤ m := (le_max_left _ _).trans hlow
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmone
  have hN : (N : ℝ) ≤ m := (le_max_right _ _).trans hlow
  have hhigh : max (2 * ((Fintype.card V : ℝ) - 1) / 3)
      (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2)) ≤ m :=
    (le_max_right _ _).trans hm
  have hsize := (le_max_left _ _).trans hhigh
  have hrate := (le_max_right _ _).trans hhigh
  have hrate' : (Fintype.card V : ℝ) - 1 ≤ (m : ℝ) * (6 * η ^ 2) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * η ^ 2)).mp hrate
  refine ⟨m, by exact_mod_cast hN, Nat.cast_pos.mp hmpos, ?_⟩
  refine (cubeSlope_totalVariation V m (Nat.cast_pos.mp hmpos) hsize).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (Real.sqrt_le_left (by positivity : 0 ≤ η * 2)).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * m)).2
  nlinarith

theorem cube_expected_singletons (m : ℕ) (hm : 0 < m) :
    ((m ^ 3 : ℕ) : ℝ) * (1 / (m : ℝ) ^ 2) = m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  push_cast
  field_simp [hm']

end Singleton


variable {V : Type*} [Fintype V] [AddGroup V] [DecidableEq V]

omit [Fintype α] [DecidableEq V] in

theorem translated_uniform_intercept (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    p a * uniformWeights V (z - shift a) = p a * uniformWeights V z := rfl

theorem uniform_intercept_pushforward (shift z : V) :
    (∑ t : V, if t + shift = z then uniformWeights V t else 0) =
      uniformWeights V z := by
  classical
  simp [← eq_sub_iff_add_eq, uniformWeights]

omit [Fintype α] in
theorem joint_intercept_pushforward (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    (∑ t : V, if t + shift a = z then p a * uniformWeights V t else 0) =
      p a * uniformWeights V z := by
  classical
  calc
    _ = p a * (∑ t : V, if t + shift a = z then uniformWeights V t else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp_all
    _ = _ := by rw [uniform_intercept_pushforward]

omit [DecidableEq V] in
theorem totalVariation_append_uniform_intercept (p q : α → ℝ) :
    totalVariation (fun az : α × V => p az.1 * uniformWeights V az.2)
      (fun az : α × V => q az.1 * uniformWeights V az.2) = totalVariation p q := by
  exact DFVSGames.Foundations.Repetition.totalVariation_append_kernel p q
    (fun _ => uniformWeights V) (fun _ => uniformWeights_isProbability)


end
end DFVSGames.Decoder.SparseLaw


namespace DFVSGames.Soundness.PartnerProjection

inductive Slot where
  | first | second | third
  deriving DecidableEq, Repr

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def zeroTriple : Triple := ⟨false, false, false⟩

def parity (x : Triple) : Bool := (x.first.xor x.second).xor x.third

def addTriple (x y : Triple) : Triple :=
  ⟨x.first.xor y.first, x.second.xor y.second, x.third.xor y.third⟩

theorem parity_add (x y : Triple) :
    parity (addTriple x y) = (parity x).xor (parity y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem and_xor (b h h' : Bool) :
    (b && h).xor (b && h') = (b && h.xor h') := by
  cases b <;> cases h <;> cases h' <;> decide

def retained (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.first
  | .second => x.second
  | .third => x.third

def freeBit (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.second
  | .second => x.first
  | .third => x.first

theorem retained_add (s : Slot) (x y : Triple) :
    retained s (addTriple x y) = (retained s x).xor (retained s y) := by
  cases s <;> rfl

theorem freeBit_add (s : Slot) (x y : Triple) :
    freeBit s (addTriple x y) = (freeBit s x).xor (freeBit s y) := by
  cases s <;> rfl

def complete (s : Slot) (p r f : Bool) : Triple :=
  match s with
  | .first => ⟨r, f, (p.xor r).xor f⟩
  | .second => ⟨f, r, (p.xor r).xor f⟩
  | .third => ⟨f, (p.xor r).xor f, r⟩

theorem parity_complete (s : Slot) (p r f : Bool) :
    parity (complete s p r f) = p := by
  cases s <;> cases p <;> cases r <;> cases f <;> decide

theorem retained_complete (s : Slot) (p r f : Bool) :
    retained s (complete s p r f) = r := by
  cases s <;> rfl

theorem freeBit_complete (s : Slot) (p r f : Bool) :
    freeBit s (complete s p r f) = f := by
  cases s <;> rfl

theorem complete_coordinates (s : Slot) (x : Triple) :
    complete s (parity x) (retained s x) (freeBit s x) = x := by
  rcases x with ⟨a, b, c⟩
  cases s <;> cases a <;> cases b <;> cases c <;> decide

theorem retained_zero (s : Slot) : retained s zeroTriple = false := by
  cases s <;> rfl

theorem freeBit_zero (s : Slot) : freeBit s zeroTriple = false := by
  cases s <;> rfl

theorem complete_zero (s : Slot) : complete s false false false = zeroTriple := by
  cases s <;> rfl

theorem complete_kernel_add (s : Slot) (a b : Bool) :
    complete s false false (a.xor b) =
      addTriple (complete s false false a) (complete s false false b) := by
  cases s <;> cases a <;> cases b <;> decide

variable {Position : Type} (rhs active : Position → Bool) (slot : Position → Slot)

structure SourcePoint where
  homogeneous : Bool
  coordinates : Position → Triple
  valid : ∀ j, parity (coordinates j) = (rhs j && homogeneous)

structure PartnerPoint where
  homogeneous : Bool
  full : Position → Triple
  single : Position → Bool
  full_zero : ∀ j, active j = true → full j = zeroTriple
  full_valid : ∀ j, active j = false → parity (full j) = (rhs j && homogeneous)
  single_zero : ∀ j, active j = false → single j = false

theorem source_ext {x y : SourcePoint rhs}
    (hh : x.homogeneous = y.homogeneous) (hx : x.coordinates = y.coordinates) : x = y := by
  cases x
  cases y
  cases hh
  cases hx
  rfl

theorem partner_ext {x y : PartnerPoint rhs active}
    (hh : x.homogeneous = y.homogeneous) (hf : x.full = y.full)
    (hs : x.single = y.single) : x = y := by
  cases x
  cases y
  cases hh
  cases hf
  cases hs
  rfl

def project (x : SourcePoint rhs) : PartnerPoint rhs active where
  homogeneous := x.homogeneous
  full := fun j => if active j then zeroTriple else x.coordinates j
  single := fun j => if active j then retained (slot j) (x.coordinates j) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simpa [hj] using x.valid j
  single_zero := by intro j hj; simp [hj]

def lift (y : PartnerPoint rhs active) : SourcePoint rhs where
  homogeneous := y.homogeneous
  coordinates := fun j =>
    if active j then complete (slot j) (rhs j && y.homogeneous) (y.single j) false
    else y.full j
  valid := by
    intro j
    cases hj : active j with
    | false => simpa [hj] using y.full_valid j hj
    | true => simp [parity_complete]

theorem project_lift (y : PartnerPoint rhs active) :
    project rhs active slot (lift rhs active slot y) = y := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j with
    | false => simp [project, lift, hj]
    | true => simpa [project, hj] using (y.full_zero j hj).symm
  · funext j
    cases hj : active j with
    | false => simpa [project, hj] using (y.single_zero j hj).symm
    | true => simp [project, lift, hj, retained_complete]

theorem project_surjective :
    ∀ y : PartnerPoint rhs active, ∃ x : SourcePoint rhs, project rhs active slot x = y := by
  intro y
  exact ⟨lift rhs active slot y, project_lift rhs active slot y⟩

theorem homogeneous_preserved (x : SourcePoint rhs) :
    (project rhs active slot x).homogeneous = x.homogeneous := rfl

def zeroSource : SourcePoint rhs where
  homogeneous := false
  coordinates := fun _ => zeroTriple
  valid := by intro j; simp [parity, zeroTriple]

def zeroPartner : PartnerPoint rhs active where
  homogeneous := false
  full := fun _ => zeroTriple
  single := fun _ => false
  full_zero := by intros; rfl
  full_valid := by intros; simp [parity, zeroTriple]
  single_zero := by intros; rfl

def addSource (x y : SourcePoint rhs) : SourcePoint rhs where
  homogeneous := x.homogeneous.xor y.homogeneous
  coordinates := fun j => addTriple (x.coordinates j) (y.coordinates j)
  valid := by
    intro j
    rw [parity_add, x.valid, y.valid, and_xor]

def addPartner (x y : PartnerPoint rhs active) : PartnerPoint rhs active where
  homogeneous := x.homogeneous.xor y.homogeneous
  full := fun j => addTriple (x.full j) (y.full j)
  single := fun j => (x.single j).xor (y.single j)
  full_zero := by
    intro j hj
    rw [x.full_zero j hj, y.full_zero j hj]
    rfl
  full_valid := by
    intro j hj
    rw [parity_add, x.full_valid j hj, y.full_valid j hj, and_xor]
  single_zero := by
    intro j hj
    rw [x.single_zero j hj, y.single_zero j hj]
    rfl

theorem project_add (x y : SourcePoint rhs) :
    project rhs active slot (addSource rhs x y) =
      addPartner rhs active (project rhs active slot x) (project rhs active slot y) := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, addTriple, zeroTriple]
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, retained_add]

theorem project_zero :
    project rhs active slot (zeroSource rhs) = zeroPartner rhs active := by
  apply partner_ext
  · rfl
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner]
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner, retained_zero]

def InKernel (x : SourcePoint rhs) : Prop :=
  project rhs active slot x = zeroPartner rhs active

theorem kernel_characterization (x : SourcePoint rhs) :
    InKernel rhs active slot x ↔
      x.homogeneous = false ∧
      (∀ j, active j = false → x.coordinates j = zeroTriple) ∧
      (∀ j, active j = true → retained (slot j) (x.coordinates j) = false) := by
  constructor
  · intro hx
    refine ⟨congrArg PartnerPoint.homogeneous hx, ?_, ?_⟩
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.full j) hx
      simpa [project, zeroPartner, hj] using h
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.single j) hx
      simpa [project, zeroPartner, hj] using h
  · rintro ⟨hh, hf, hs⟩
    apply partner_ext
    · exact hh
    · funext j
      cases hj : active j with
      | false => simpa [project, zeroPartner, hj] using hf j hj
      | true => simp [project, zeroPartner, hj]
    · funext j
      cases hj : active j with
      | false => simp [project, zeroPartner, hj]
      | true => simpa [project, zeroPartner, hj] using hs j hj

structure ActiveBits where
  coefficient : Position → Bool
  inactive_zero : ∀ j, active j = false → coefficient j = false

theorem activeBits_ext {a b : ActiveBits active}
    (h : a.coefficient = b.coefficient) : a = b := by
  cases a
  cases b
  cases h
  rfl

def addActiveBits (a b : ActiveBits active) : ActiveBits active where
  coefficient := fun j => (a.coefficient j).xor (b.coefficient j)
  inactive_zero := by
    intro j hj
    rw [a.inactive_zero j hj, b.inactive_zero j hj]
    rfl

def kernelPoint (a : ActiveBits active) : SourcePoint rhs where
  homogeneous := false
  coordinates := fun j => complete (slot j) false false (a.coefficient j)
  valid := by intro j; simp [parity_complete]

theorem kernelPoint_add (a b : ActiveBits active) :
    kernelPoint rhs active slot (addActiveBits active a b) =
      addSource rhs (kernelPoint rhs active slot a) (kernelPoint rhs active slot b) := by
  apply source_ext
  · rfl
  · funext j
    exact complete_kernel_add _ _ _

theorem kernelPoint_mem (a : ActiveBits active) :
    InKernel rhs active slot (kernelPoint rhs active slot a) := by
  apply (kernel_characterization rhs active slot _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj
    simp [kernelPoint, a.inactive_zero j hj, complete_zero]
  · intro j _
    exact retained_complete _ _ _ _

def kernelCoefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ActiveBits active where
  coefficient := fun j => freeBit (slot j) (x.coordinates j)
  inactive_zero := by
    intro j hj
    have hf := (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj
    rw [hf, freeBit_zero]

theorem kernelPoint_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    kernelPoint rhs active slot (kernelCoefficients rhs active slot x hx) = x := by
  have hc := (kernel_characterization rhs active slot x).1 hx
  apply source_ext
  · exact hc.1.symm
  · funext j
    have hp : parity (x.coordinates j) = false := by
      rw [x.valid j, hc.1]
      simp
    have hr : retained (slot j) (x.coordinates j) = false := by
      cases hj : active j with
      | false => rw [hc.2.1 j hj, retained_zero]
      | true => exact hc.2.2 j hj
    simpa [kernelPoint, kernelCoefficients, hp, hr] using
      complete_coordinates (slot j) (x.coordinates j)

theorem coefficients_kernelPoint (a : ActiveBits active) :
    kernelCoefficients rhs active slot (kernelPoint rhs active slot a)
      (kernelPoint_mem rhs active slot a) = a := by
  apply activeBits_ext active
  funext j
  exact freeBit_complete _ _ _ _

theorem kernelPoint_injective (a b : ActiveBits active)
    (h : kernelPoint rhs active slot a = kernelPoint rhs active slot b) : a = b := by
  have hc : a.coefficient = b.coefficient := by
    funext j
    have he := congrArg (fun x : SourcePoint rhs => freeBit (slot j) (x.coordinates j)) h
    simpa [kernelPoint, freeBit_complete] using he
  cases a
  cases b
  cases hc
  rfl

theorem kernel_unique_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ∃ a : ActiveBits active, kernelPoint rhs active slot a = x ∧
      ∀ b : ActiveBits active, kernelPoint rhs active slot b = x → b = a := by
  refine ⟨kernelCoefficients rhs active slot x hx,
    kernelPoint_coefficients rhs active slot x hx, ?_⟩
  intro b hb
  apply kernelPoint_injective rhs active slot
  exact hb.trans (kernelPoint_coefficients rhs active slot x hx).symm

def extendActive (f : {j : Position // active j = true} → Bool) : ActiveBits active where
  coefficient := fun j => if hj : active j = true then f ⟨j, hj⟩ else false
  inactive_zero := by intro j hj; simp [hj]

theorem kernel_realizes_active
    (f : {j : Position // active j = true} → Bool) :
    ∃ x : SourcePoint rhs, InKernel rhs active slot x ∧
      ∀ j (hj : active j = true), freeBit (slot j) (x.coordinates j) = f ⟨j, hj⟩ := by
  refine ⟨kernelPoint rhs active slot (extendActive active f),
    kernelPoint_mem rhs active slot _, ?_⟩
  intro j hj
  simp [kernelPoint, freeBit_complete, extendActive, hj]

theorem kernel_determined_by_active
    (x y : SourcePoint rhs)
    (hx : InKernel rhs active slot x) (hy : InKernel rhs active slot y)
    (hfree : ∀ j, active j = true →
      freeBit (slot j) (x.coordinates j) = freeBit (slot j) (y.coordinates j)) : x = y := by
  have hc : kernelCoefficients rhs active slot x hx = kernelCoefficients rhs active slot y hy := by
    apply activeBits_ext active
    funext j
    cases hj : active j with
    | false =>
      simp [kernelCoefficients,
        (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj,
        (kernel_characterization rhs active slot y).1 hy |>.2.1 j hj]
    | true => exact hfree j hj
  have hp := congrArg (kernelPoint rhs active slot) hc
  simpa only [kernelPoint_coefficients] using hp

theorem disjoint_kernels_intersection_zero
    (active' : Position → Bool) (slot' : Position → Slot)
    (hdisjoint : ∀ j, active j = true → active' j = false)
    (x : SourcePoint rhs)
    (hx : InKernel rhs active slot x)
    (hx' : InKernel rhs active' slot' x) : x = zeroSource rhs := by
  have h := (kernel_characterization rhs active slot x).1 hx
  have h' := (kernel_characterization rhs active' slot' x).1 hx'
  apply source_ext
  · exact h.1
  · funext j
    cases hj : active j with
    | false => exact h.2.1 j hj
    | true => exact h'.2.1 j (hdisjoint j hj)

end DFVSGames.Soundness.PartnerProjection

end OAI
