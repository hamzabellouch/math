import Mathlib.Probability.Kernel.Composition.Comp

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelPotential

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

noncomputable def potential (B : Kernel α β) (K : Kernel α α) : Kernel α β :=
  Kernel.sum (fun n : ℕ => B ∘ₖ (K ^ n))

instance potential_isSFiniteKernel (B : Kernel α β) (K : Kernel α α)
    [IsSFiniteKernel B] [IsSFiniteKernel K] : IsSFiniteKernel (potential B K) := by
  have hp : ∀ n : ℕ, IsSFiniteKernel (K ^ n) := by
    intro n
    induction n with
    | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
    | succ n ih =>
      rw [pow_succ]
      change IsSFiniteKernel ((K ^ n) ∘ₖ K)
      infer_instance
  unfold potential
  infer_instance

theorem compose_mono_left {B C : Kernel α β} (h : B ≤ C) (K : Kernel γ α) :
    B ∘ₖ K ≤ C ∘ₖ K := by
  intro a
  apply Measure.le_iff.mpr
  intro s hs
  rw [Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  exact lintegral_mono (fun x => h x s)

theorem compose_finset_sum_left (I : Finset ℕ) (B : ℕ → Kernel α β) (K : Kernel γ α) :
    (∑ n ∈ I, B n) ∘ₖ K = ∑ n ∈ I, B n ∘ₖ K := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert n I hn ih => simp only [Finset.sum_insert hn, Kernel.comp_add_left, ih]

theorem power_comp_succ (B : Kernel α β) (K : Kernel α α) (n : ℕ) :
    B ∘ₖ (K ^ (n + 1)) = (B ∘ₖ (K ^ n)) ∘ₖ K := by
  rw [pow_succ]
  exact (Kernel.comp_assoc B (K ^ n) K).symm

theorem potential_unfold (B : Kernel α β) (K : Kernel α α) :
    potential B K = B + (potential B K) ∘ₖ K := by
  unfold potential
  rw [Kernel.comp_sum_left]
  ext a s hs
  rw [Kernel.sum_apply' _ _ hs, add_apply, Measure.add_apply, Kernel.sum_apply' _ _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  have hz : B ∘ₖ (K ^ 0) = B := Kernel.comp_id B
  simp only [hz, power_comp_succ]

theorem potential_le_of_super (B : Kernel α β) (K : Kernel α α) (S : Kernel α β)
    (hS : B + S ∘ₖ K ≤ S) : potential B K ≤ S := by
  have hfin : ∀ n : ℕ, (∑ j ∈ Finset.range n, B ∘ₖ (K ^ j)) ≤ S := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact bot_le
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have hz : B ∘ₖ (K ^ 0) = B := Kernel.comp_id B
      simp only [hz, power_comp_succ]
      rw [← compose_finset_sum_left]
      calc
        _ = B + (∑ j ∈ Finset.range n, B ∘ₖ (K ^ j)) ∘ₖ K := add_comm _ _
        _ ≤ B + S ∘ₖ K := fun a => add_le_add le_rfl ((compose_mono_left ih K) a)
        _ ≤ S := hS
  intro a
  apply Measure.le_iff.mpr
  intro s hs
  rw [potential, Kernel.sum_apply' _ _ hs, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  have h := hfin n a s
  rwa [Kernel.finsetSum_apply'] at h

theorem potential_add (B C : Kernel α β) (K : Kernel α α) :
    potential (B + C) K = potential B K + potential C K := by
  unfold potential
  simp_rw [Kernel.comp_add_left]
  exact Kernel.sum_add _ _

theorem potential_comp_left (B : Kernel α β) (C : Kernel β γ) (K : Kernel α α) :
    potential (C ∘ₖ B) K = C ∘ₖ (potential B K) := by
  unfold potential
  rw [Kernel.comp_sum_right]
  congr 1
  funext n
  exact Kernel.comp_assoc C B (K ^ n)

theorem first_capture_decomposition (B : Kernel α β) (Q H : Kernel α α) :
    potential B (Q + H) = potential (potential B Q) (potential H Q) := by
  let P := potential B (Q + H)
  let O := potential B Q
  let R := potential H Q
  let S := potential O R
  have hP : P = B + P ∘ₖ (Q + H) := potential_unfold B (Q + H)
  have hO : O = B + O ∘ₖ Q := potential_unfold B Q
  have hR : R = H + R ∘ₖ Q := potential_unfold H Q
  have hS : S = O + S ∘ₖ R := potential_unfold O R
  have hSeq : B + S ∘ₖ (Q + H) = S := by
    calc
      _ = B + S ∘ₖ Q + S ∘ₖ H := by rw [Kernel.comp_add_right]; abel
      _ = B + (O + S ∘ₖ R) ∘ₖ Q + S ∘ₖ H := by rw [← hS]
      _ = (B + O ∘ₖ Q) + S ∘ₖ (H + R ∘ₖ Q) := by
        rw [Kernel.comp_add_left, Kernel.comp_add_right, ← Kernel.comp_assoc]
        abel
      _ = O + S ∘ₖ R := by rw [← hO, ← hR]
      _ = S := hS.symm
  have hPS : P ≤ S := potential_le_of_super B (Q + H) S hSeq.le
  have hPsuper : (B + P ∘ₖ H) + P ∘ₖ Q ≤ P := by
    have heq : (B + P ∘ₖ H) + P ∘ₖ Q = P := by
      calc
        _ = B + P ∘ₖ (Q + H) := by rw [Kernel.comp_add_right]; abel
        _ = P := hP.symm
    exact heq.le
  have hOR : O + P ∘ₖ R ≤ P := by
    have h := potential_le_of_super (B + P ∘ₖ H) Q P hPsuper
    rw [potential_add, potential_comp_left] at h
    exact h
  have hSP : S ≤ P := potential_le_of_super O R P hOR
  exact le_antisymm hPS hSP

end NumberTheoryLean.KernelPotential

end

end Erdos970

end OAI
