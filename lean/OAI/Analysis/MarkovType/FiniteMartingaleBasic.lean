import OAI.Analysis.MarkovType.FiniteProbability
import OAI.Analysis.MarkovType.FiniteStoppingTime
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteDifference (M : ℕ → Ω → E) (j : ℕ) : Ω → E :=
  if j = 0 then M 0 else fun ω => M j ω - M (j - 1) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_zero [Fintype Ω] [NormedSpace ℝ E] (M : ℕ → Ω → E) :
    finiteDifference M 0 = M 0 := by
  simp [finiteDifference]

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_succ [Fintype Ω] [NormedSpace ℝ E] (M : ℕ → Ω → E) (j : ℕ) (ω : Ω) :
    finiteDifference M (j + 1) ω = M (j + 1) ω - M j ω := by
  simp [finiteDifference]

theorem finiteDifference_telescope (M : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    M n ω = M 0 ω + ∑ j ∈ Finset.range n, finiteDifference M (j + 1) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, finiteDifference_succ M n ω]
    rw [← add_assoc, ← ih]
    abel

def HasZeroConditionalSum (μ : FiniteLaw Ω) (P : Setoid Ω) (f : Ω → E) : Prop :=
  ∀ a : Ω, ∑ ω, (if P.r ω a then μ.mass ω • f ω else 0) = 0

theorem hasZeroConditionalSum_zero (μ : FiniteLaw Ω) (P : Setoid Ω) :
    HasZeroConditionalSum μ P (fun _ => (0 : E)) := by
  classical
  intro a
  simp

theorem HasZeroConditionalSum.add {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f g : Ω → E} (hf : HasZeroConditionalSum μ P f)
    (hg : HasZeroConditionalSum μ P g) :
    HasZeroConditionalSum μ P (fun ω => f ω + g ω) := by
  classical
  intro a
  calc
    _ = (∑ ω, if P.r ω a then μ.mass ω • f ω else 0) +
        ∑ ω, if P.r ω a then μ.mass ω • g ω else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : P.r ω a <;> simp [h, smul_add]
    _ = 0 := by rw [hf a, hg a, add_zero]

theorem HasZeroConditionalSum.predictable_smul {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (c : Ω → ℝ)
    (hc : ∀ {ω η}, P.r ω η → c ω = c η) :
    HasZeroConditionalSum μ P (fun ω => c ω • f ω) := by
  classical
  intro a
  calc
    _ = c a • ∑ ω, if P.r ω a then μ.mass ω • f ω else 0 := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : P.r ω a
      · simp only [ite_eq_left h, hc h]
        rw [smul_smul, smul_smul, mul_comm]
      · simp [h]
    _ = 0 := by rw [hf a, smul_zero]

theorem HasZeroConditionalSum.indicator {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (A : Ω → Prop)
    (hA : ∀ {ω η}, P.r ω η → (A ω ↔ A η)) :
    HasZeroConditionalSum μ P (fun ω => if A ω then f ω else 0) := by
  classical
  have h := hf.predictable_smul (fun ω => if A ω then (1 : ℝ) else 0) (by
    intro ω η hωη
    simp only [hA hωη])
  simpa only [ite_smul, one_smul, zero_smul] using h

namespace FinitePartitionFiltration

def IsMartingaleUpTo (F : FinitePartitionFiltration Ω) (μ : FiniteLaw Ω)
    (M : ℕ → Ω → E) (N : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j)) ∧
  ∀ j : ℕ, 0 < j → j ≤ N →
    HasZeroConditionalSum μ (F.part (j - 1)) (finiteDifference M j)

theorem IsMartingaleUpTo.mono {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {n N : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (hn : n ≤ N) :
    F.IsMartingaleUpTo μ M n :=
  ⟨fun j hj => hM.1 j (hj.trans hn), fun j hj hjn => hM.2 j hj (hjn.trans hn)⟩

theorem IsMartingaleUpTo.difference_adapted {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {N j : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (hj : j ≤ N) :
    F.AdaptedAt j (finiteDifference M j) := by
  unfold AdaptedAt
  intro ω η hωη
  by_cases hj0 : j = 0
  · subst j
    simpa only [finiteDifference_zero] using hM.1 0 hj hωη
  · simp only [finiteDifference, ite_eq_right hj0]
    rw [hM.1 j hj hωη,
      hM.1 (j - 1) ((Nat.sub_le j 1).trans hj) (F.refines (Nat.sub_le j 1) hωη)]

end FinitePartitionFiltration

def finiteL2Norm (μ : FiniteLaw Ω) (f : Ω → E) : ℝ :=
  Real.sqrt (μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)))

omit sectionNormedSpaceℝE in
theorem finiteL2Norm_nonneg [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f : Ω → E) :
    0 ≤ finiteL2Norm μ f := Real.sqrt_nonneg _

omit sectionNormedSpaceℝE in
@[simp] theorem finiteL2Norm_zero [NormedSpace ℝ E] (μ : FiniteLaw Ω) :
    finiteL2Norm μ (fun _ => (0 : E)) = 0 := by
  simp [finiteL2Norm, FiniteLaw.expect]

omit sectionNormedSpaceℝE in
theorem finiteL2Norm_sq [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ f ^ (2 : ℕ) = μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) :=
  Real.sq_sqrt (μ.expect_nonneg fun _ω => sq_nonneg _)

def FiniteUpperL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r χ : ℝ) : Prop :=
  ∀ m : ℕ, ∀ μ : FiniteLaw (Fin m),
  ∀ F : FinitePartitionFiltration (Fin m), ∀ M : ℕ → Fin m → E,
  ∀ N : ℕ, ∀ B : ℝ, 0 ≤ B → F.IsMartingaleUpTo μ M N →
    (∀ j : ℕ, j ≤ N → finiteL2Norm μ (finiteDifference M j) ≤ B) →
    finiteL2Norm μ (M N) ≤ χ * (N + 1 : ℝ) ^ (1 / r) * B

def FiniteLowerL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s χ : ℝ) : Prop :=
  ∀ m : ℕ, ∀ μ : FiniteLaw (Fin m),
  ∀ F : FinitePartitionFiltration (Fin m), ∀ M : ℕ → Fin m → E,
  ∀ N : ℕ, F.IsMartingaleUpTo μ M N →
    (∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference M j)) ≤
      χ * (N + 1 : ℝ) ^ (1 - 1 / s) * finiteL2Norm μ (M N)

end MarkovSuperreflexivity

end

end OAI
