import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
open scoped BigOperators

noncomputable def weightedMoment {α : Type*} (C : Finset α) (w f : α → ℝ) : ℝ :=
  ∑ x ∈ C, w x * f x

noncomputable def indicatorSum {ι α : Type*} (J : Finset ι) (I : ι → α → ℝ) (x : α) : ℝ :=
  ∑ j ∈ J, I j x

theorem moment_sum {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (f : ι → α → ℝ) :
    weightedMoment C w (fun x => ∑ j ∈ J, f j x) = ∑ j ∈ J, weightedMoment C w (f j) := by
  unfold weightedMoment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem moment_indicator_square {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (I : ι → α → ℝ) :
    weightedMoment C w (fun x => (indicatorSum J I x)^2) =
      ∑ i ∈ J, ∑ j ∈ J, weightedMoment C w (fun x => I i x * I j x) := by
  have he (x : α) : (indicatorSum J I x)^2 = ∑ i ∈ J, ∑ j ∈ J, I i x * I j x := by
    rw [indicatorSum, pow_two, Finset.sum_mul_sum]
  simp only [he, moment_sum]

theorem centered_moment_identity {α : Type*} (C : Finset α) (w f : α → ℝ) (M : ℝ) :
    weightedMoment C w (fun x => (f x-M)^2) =
      weightedMoment C w (fun x => (f x)^2) - 2*M*weightedMoment C w f +
        M^2*(∑ x ∈ C, w x) := by
  unfold weightedMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem stable_finite_variance {ι α : Type*} (C : Finset α) (w : α → ℝ)
    (J : Finset ι) (I : ι → α → ℝ) (K : ι → ι → ℝ) (V zeta : ℝ)
    (hV : 0 ≤ V) (hzeta : 0 ≤ zeta)
    (hI : ∀ j ∈ J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1)
    (hMass : (∑ x ∈ C, w x) ≤ 1+zeta)
    (hLower : ∀ j ∈ J, (1-zeta)*V ≤ weightedMoment C w (I j))
    (hUpper : ∀ j ∈ J, weightedMoment C w (I j) ≤ (1+zeta)*V)
    (hPair : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*K i j)
    (hDiag : ∀ j ∈ J, K j j = V)
    (hModel : (∑ i ∈ J, ∑ j ∈ J, K i j) ≤ ((J.card : ℝ)*V)^2+(J.card : ℝ)*V) :
    weightedMoment C w (fun x => (indicatorSum J I x-(J.card : ℝ)*V)^2) ≤
      (1+zeta)*((J.card : ℝ)*V)+4*zeta*((J.card : ℝ)*V)^2 := by
  classical
  let M := (J.card : ℝ)*V
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) hV
  have hMean : (1-zeta)*M ≤ weightedMoment C w (indicatorSum J I) := by
    change (1-zeta)*M ≤ weightedMoment C w (fun x => ∑ j ∈ J, I j x)
    rw [moment_sum]
    have h := Finset.sum_le_sum (fun j hj => hLower j hj)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    dsimp only [M]
    nlinarith [h]
  have hAll : ∀ i ∈ J, ∀ j ∈ J,
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*K i j := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      have he : weightedMoment C w (fun x => I i x*I i x) = weightedMoment C w (I i) := by
        unfold weightedMoment
        apply Finset.sum_congr rfl
        intro x hx
        rcases hI i hi x hx with h | h <;> simp [h]
      rw [he, hDiag i hi]
      exact hUpper i hi
    · exact hPair i hi j hj hij
  have hSecond : weightedMoment C w (fun x => (indicatorSum J I x)^2) ≤ (1+zeta)*(M^2+M) := by
    rw [moment_indicator_square]
    calc
      _ ≤ ∑ i ∈ J, ∑ j ∈ J, (1+zeta)*K i j :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hAll i hi j hj))
      _ = (1+zeta)*(∑ i ∈ J, ∑ j ∈ J, K i j) := by simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hModel (by linarith)
  have hMeanScaled := mul_le_mul_of_nonneg_left hMean (show 0 ≤ 2*M by positivity)
  have hMassScaled := mul_le_mul_of_nonneg_left hMass (sq_nonneg M)
  change weightedMoment C w (fun x => (indicatorSum J I x-M)^2) ≤ (1+zeta)*M+4*zeta*M^2
  rw [centered_moment_identity]
  nlinarith [hSecond, hMeanScaled, hMassScaled]

end ErdosRandomVariance

end

end Erdos970

end OAI
