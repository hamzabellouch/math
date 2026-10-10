import OAI.NumberTheory.TwoPoint.Walks.RankProbability
import OAI.NumberTheory.TwoPoint.Bounds.ZeroRows
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The finite random-prime rank estimate, manuscript `q:rank-probability`. -/

namespace TwoPointCorrelations

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primeDifference (P : Finset ℕ) (B : Matrix ι ι ℤ)
    (y z : ι → P) : ι → ℤ :=
  B *ᵥ ((fun j => ((y j).val : ℤ)) - (fun j => ((z j).val : ℤ)))

lemma average_probability_comm {A C : Type*} [Fintype A] [Fintype C]
    (μ : FiniteLaw A) (ν : FiniteLaw C) (E : A → C → Prop) :
    μ.average (fun x => ν.probability (E x)) =
      ν.average (fun y => μ.probability (fun x => E x y)) := by
  simp only [FiniteLaw.probability, FiniteLaw.average, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring

theorem random_prime_rank_squared
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (f : (ι → P) → ι → ℤ)
    (M : ℕ) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ p, μ.weight p ≤ α)
    (hsize : ∀ y z : ι → P, ∀ i, (primeDifference P B y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ι => μ)
    (ν.average (fun c => ν.probability (fun y =>
      ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i))) ^ 2 ≤
        (α * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ι := by
  classical
  dsimp only
  let ν := FiniteLaw.independent (fun _ : ι => μ)
  let E (c y : ι → P) : Prop :=
    ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i
  let D (c y z : ι → P) : Prop := ∀ i, ((c i).val : ℤ) ∣ primeDifference P B y z i
  have hd (c y z : ι → P) (hy : E c y) (hz : E c z) : D c y z := by
    intro i
    have h := dvd_sub (hy i) (hz i)
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub, primeDifference, Matrix.mulVec_sub,
      Pi.sub_apply] using h
  have hs := FiniteLaw.two_sample_bound ν ν E D hd
  have hreorder : ν.average (fun c => ν.average (fun y => ν.probability (D c y))) =
      (ν.product ν).average (fun yz => ν.probability (fun c => D c yz.1 yz.2)) := by
    rw [FiniteLaw.average_product, ν.average_comm]
    apply congrArg (ν.average)
    funext y
    exact average_probability_comm ν ν (fun c z => D c y z)
  rw [hreorder] at hs
  let β := α * (Nat.log 2 M : ℝ)
  have hβ : 0 ≤ β := mul_nonneg hα (Nat.cast_nonneg _)
  have hcontrols (y z : ι → P) :
      ν.probability (fun c => D c y z) ≤
        ∏ i, if primeDifference P B y z i = 0 then (1 : ℝ) else β := by
    rw [show ν.probability (fun c => D c y z) =
        ∏ i, μ.probability (fun p => (p.val : ℤ) ∣ primeDifference P B y z i) from
          FiniteLaw.independent_probability_all (fun _ : ι => μ)
            (fun i p => (p.val : ℤ) ∣ primeDifference P B y z i)]
    apply prod_le_prod₀
    · intro i _
      exact μ.probability_nonneg _
    · intro i _
      by_cases hi : primeDifference P B y z i = 0
      · simp [hi, FiniteLaw.probability]
      · rw [ite_eq_right hi]
        apply (FiniteLaw.prime_divisibility_probability P hP μ α hα hatom _ hi).trans
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.log_mono_right (hsize y z i)) hα
  have hzero (S : Finset ι) :
      (ν.product ν).average (fun yz =>
        ∏ i ∈ S, if primeDifference P B yz.1 yz.2 i = 0 then (1 : ℝ) else 0) ≤ α ^ S.card := by
    rw [FiniteLaw.average_product, ν.average_comm]
    apply (ν.average_mono (g := fun _ => α ^ S.card) ?_).trans_eq (ν.average_const _)
    intro z
    have heq : ν.average (fun x =>
        ∏ i ∈ S, if primeDifference P B x z i = 0 then (1 : ℝ) else 0) =
        ν.probability (fun x => ∀ i ∈ S, primeDifference P B x z i = 0) := by
      unfold FiniteLaw.probability
      apply congrArg ν.average
      funext x
      by_cases hx : ∀ i ∈ S, primeDifference P B x z i = 0 <;>
        simp [Finset.prod_boole, hx]
    rw [heq]
    have hv : Function.Injective (fun p : P => (p.val : ℤ)) := by
      intro p q hpq
      apply Subtype.ext
      exact Int.ofNat_inj.mp hpq
    exact FiniteLaw.zero_rows_probability (fun _ : ι => μ)
      (fun p : P => (p.val : ℤ)) hv
      B hB S z α hα (fun _ => hatom)
  calc
    _ ≤ (ν.product ν).average (fun yz => ν.probability (fun c => D c yz.1 yz.2)) := hs
    _ ≤ (ν.product ν).average (fun yz =>
        ∏ i, if primeDifference P B yz.1 yz.2 i = 0 then (1 : ℝ) else β) :=
      (ν.product ν).average_mono (fun yz => hcontrols yz.1 yz.2)
    _ ≤ (α + β) ^ Fintype.card ι :=
      FiniteLaw.zero_set_product_bound (ν.product ν) (fun yz => primeDifference P B yz.1 yz.2)
        α β hβ hzero
    _ = _ := by congr 1; dsimp [β]; ring

/-- The square-root form of the rank bound. -/
theorem random_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (f : (ι → P) → ι → ℤ)
    (M : ℕ) (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ p, μ.weight p ≤ α)
    (hsize : ∀ y z : ι → P, ∀ i, (primeDifference P B y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ι => μ)
    ν.average (fun c => ν.probability (fun y =>
      ∀ i, ((c i).val : ℤ) ∣ (B *ᵥ (fun j => ((y j).val : ℤ)) + f c) i)) ≤
        Real.sqrt ((α * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ι) := by
  exact Real.le_sqrt_of_sq_le (random_prime_rank_squared P hP μ B hB f M α hα hatom hsize)

end TwoPointCorrelations

end OAI
