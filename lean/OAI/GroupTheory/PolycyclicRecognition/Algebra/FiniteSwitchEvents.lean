import OAI.GroupTheory.PolycyclicRecognition.Algebra.IndependentSwitchParameters

namespace OAI

/-! # Successful switch events only use the prescribed finite list of sheets -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G]

omit [MeasurableSpace G] in
theorem switchSuccessful_mono (S R : ℕ → Set G) (n k : ℕ)
    (hsub : ∀ j, n < j → j ≤ n + k → S j ⊆ R j)
    (x : G) (p : SwitchParameters G k)
    (hp : SwitchSuccessful S n k x p) : SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => trivial
  | succ k ih =>
    exact ⟨hsub (n + 1) (by omega) (by omega) hp.1,
      ih (n + 1) (fun j hj hj' => hsub j (by omega) (by omega)) _ p.2.2 hp.2⟩

omit [MeasurableSpace G] in
theorem switchSuccessful_congr (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j)
    (x : G) (p : SwitchParameters G k) :
    SwitchSuccessful S n k x p ↔ SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    change (_ ∈ S (n + 1) ∧ _) ↔ (_ ∈ R (n + 1) ∧ _)
    rw [heq (n + 1) (by omega) (by omega)]
    exact and_congr_right (fun _ => ih (n + 1)
      (fun j hj hj' => heq j (by omega) (by omega)) _ p.2.2)

theorem survivingSwitchProbability_congr (σ : ℕ → Measure G)
    (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j) (x : G) :
    survivingSwitchProbability σ S n k x = survivingSwitchProbability σ R n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    simp only [survivingSwitchProbability]
    apply lintegral_congr
    intro s₁
    apply lintegral_congr
    intro s₂
    rw [heq (n + 1) (by omega) (by omega)]
    exact congrFun (indicator_congr (fun y _ =>
      ih (n + 1) (fun j hj hj' => heq j (by omega) (by omega)) y)) _

/-- No measurability conditions on unused sheets are needed. -/
theorem switchParameterLaw_success_finite [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (n k : ℕ)
    (hS : ∀ j, n < j → j ≤ n + k → MeasurableSet (S j)) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} ∧
      switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
        survivingSwitchProbability σ S n k x := by
  let R := fun j => if n < j ∧ j ≤ n + k then S j else ∅
  have hR (j : ℕ) : MeasurableSet (R j) := by
    by_cases hj : n < j ∧ j ≤ n + k
    · simpa [R, hj] using hS j hj.1 hj.2
    · simp [R, hj]
  have heq (j : ℕ) (hj : n < j) (hj' : j ≤ n + k) : S j = R j := by
    simp [R, hj, hj']
  have hsets : {p : SwitchParameters G k | SwitchSuccessful S n k x p} =
      {p | SwitchSuccessful R n k x p} := by
    ext p
    exact switchSuccessful_congr S R n k heq x p
  constructor
  · exact hsets.symm ▸ measurableSet_switchSuccessful_fixed R hR n k x
  · calc
      _ = switchParameterLaw σ n k {p | SwitchSuccessful R n k x p} :=
        congrArg (switchParameterLaw σ n k) hsets
      _ = survivingSwitchProbability σ R n k x := switchParameterLaw_success σ R hR n k x
      _ = _ := (survivingSwitchProbability_congr σ S R n k heq x).symm

end PolycyclicRecognition

end

end OAI
