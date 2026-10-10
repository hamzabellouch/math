import OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree

namespace OAI

/-! De Morgan duality transfers the sampled AND approximation to OR gates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def boolOrValue {k : ℕ} (b : Fin k → Bool) : ℝ :=
  if ∃ i, b i = true then 1 else 0

lemma boolAndValue_not {k : ℕ} (b : Fin k → Bool) :
    boolAndValue (fun i => !(b i)) = 1 - boolOrValue b := by
  have he : (∀ i, Bool.not (b i) = true) ↔ ¬∃ i, b i = true := by simp
  simp only [boolAndValue, boolOrValue, he]
  split_ifs <;> norm_num

theorem exists_composed_or_approximation {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (k s d : ℕ)
    (b : Fin k → BooleanCube n → Bool) (P : Fin k → BooleanCube n → ℝ)
    (hP : ∀ i, WalshDegreeLE (P i) d) (δ : Fin k → ℝ)
    (hδ : ∀ i, ν.probability (fun y => P i y ≠ if b i y then 1 else 0) ≤ δ i) :
    ∃ Q : BooleanCube n → ℝ,
      WalshDegreeLE Q (d * s * (Nat.log 2 k + 3)) ∧
      ν.probability (fun y => Q y ≠ boolOrValue (fun i => b i y)) ≤
        (7 / 8 : ℝ) ^ s + ∑ i, δ i := by
  let R := fun i y => 1 - P i y
  have hR (i : Fin k) : WalshDegreeLE (R i) d :=
    (WalshDegreeLE.const 1 d).sub (hP i)
  have hδ' (i : Fin k) :
      ν.probability (fun y => R i y ≠ if !(b i y) then 1 else 0) ≤ δ i := by
    apply le_trans (ν.probability_mono ?_) (hδ i)
    intro y hy heq
    apply hy
    dsimp only [R]
    rw [heq]
    cases b i y <;> norm_num
  obtain ⟨Q, hQ, he⟩ := exists_composed_and_approximation ν k s d
    (fun i y => !(b i y)) R hR δ hδ'
  refine ⟨fun y => 1 - Q y, (WalshDegreeLE.const 1 _).sub hQ, ?_⟩
  apply le_trans (ν.probability_mono ?_) he
  intro y hy heq
  apply hy
  change 1 - Q y = _
  rw [heq, boolAndValue_not]
  ring

end TwoPointCorrelations

end OAI
