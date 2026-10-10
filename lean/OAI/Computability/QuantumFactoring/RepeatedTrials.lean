import Mathlib
import OAI.Computability.QuantumFactoring.ExactnessFurther

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


/-! Exact independent-trial laws and the source's K=n^5 success guarantee. -/
namespace ExactQuantumFactoring.RepeatedTrials
open scoped BigOperators
open ExactQuantumFactoring.Exactness

noncomputable def tensorState {α : Type*} (ψ : α→ℂ) (K : ℕ) (x : Fin K→α) : ℂ :=
  ∏ i, ψ (x i)

lemma tensor_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    ∑ x : Fin K→α, Complex.normSq (tensorState ψ K x)=1 := by
  classical
  simp only [tensorState,map_prod]
  calc
    _ = (∑ x, Complex.normSq (ψ x))^K := (Fintype.sum_pow (fun x => Complex.normSq (ψ x)) K).symm
    _ = 1 := by rw [hψ,one_pow]

lemma tensor_all_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop) :
    outcomeMass (fun x : Fin K→α => ∀ i, P (x i)) (tensorState ψ K) = (outcomeMass P ψ)^K := by
  classical
  unfold outcomeMass tensorState
  calc
    _ = ∑ x : Fin K→α, ∏ i, if P (x i) then Complex.normSq (ψ (x i)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i, P (x i)
      · simp [hx,map_prod]
      · obtain ⟨i,hi⟩ := not_forall.mp hx
        rw [ite_eq_right hx]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = _ := (Fintype.sum_pow (fun x => if P x then Complex.normSq (ψ x) else 0) K).symm

lemma mass_compl {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x => ¬P x) ψ=1-outcomeMass P ψ := by
  classical
  have he : outcomeMass (fun x => ¬P x) ψ + outcomeMass P ψ = 1 := by
    unfold outcomeMass
    rw [← Finset.sum_add_distrib,← hψ]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x <;> simp [hx]
  linarith

lemma tensor_some_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x : Fin K→α => ∃ i, P (x i)) (tensorState ψ K) =
      1-(1-outcomeMass P ψ)^K := by
  classical
  have he : (fun x : Fin K→α => ∃ i, P (x i)) =
      (fun x => ¬∀ i, ¬P (x i)) := by funext x; simp
  rw [he,mass_compl _ _ (tensor_normalized ψ K hψ)]
  rw [tensor_all_mass ψ K (fun x => ¬P x),mass_compl ψ P hψ]

lemma mass_bounds {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) : 0≤outcomeMass P ψ ∧ outcomeMass P ψ≤1 := by
  classical
  unfold outcomeMass
  constructor
  · apply Finset.sum_nonneg
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith
  · rw [← hψ]
    apply Finset.sum_le_sum
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith

/-- Deliberately uses the original cutoff128 and repetition exponent5. -/
lemma repetition_failure_bound {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    (1-x)^(n^5)≤1/(2:ℝ)^(2*n) := by
  have hnR : (128:ℝ)≤n := by exact_mod_cast hn
  have hxpos : 0<x := lt_of_lt_of_le (by positivity) hx₀
  have hmul : ((n:ℝ)^5)*x ≥ 2*n := by
    have hden : (0:ℝ)<2048*(n+1) := by positivity
    have hlow := (div_le_iff₀ hden).mp hx₀
    have hnpos : (0:ℝ)<n := by positivity
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤128) hnR 3
    norm_num at hh
    have hc : (8192:ℝ)≤(n:ℝ)^3 := by linarith
    have hp : 8192*(n:ℝ)^2≤(n:ℝ)^5 := by
      simpa only [← pow_add] using mul_le_mul_of_nonneg_right hc (sq_nonneg (n:ℝ))
    have hfirst : 2*n*(2048*(n+1))≤(n:ℝ)^5 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ)≤(n:ℝ)^5)
    nlinarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hx₁) (Real.one_sub_le_exp_neg x) (n^5)
  calc
    (1-x)^(n^5) ≤ Real.exp (-x)^(n^5) := hpow
    _ = Real.exp (-(2*n:ℝ)) * Real.exp (2*n-(n:ℝ)^5*x) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-(2*n:ℝ)) := by
      have he : Real.exp (2*n-(n:ℝ)^5*x)≤1 := Real.exp_le_one_iff.mpr (by linarith)
      exact (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = 1/(Real.exp 1)^(2*n) := by
      rw [Real.exp_neg,← Real.exp_nat_mul]
      simp
    _ ≤ 1/(2:ℝ)^(2*n) := by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ (by norm_num)
      have he := Real.exp_one_gt_d9
      linarith

lemma repeated_success_lower {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    1-1/(2:ℝ)^(2*n) ≤ 1-(1-x)^(n^5) := by
  have hh := repetition_failure_bound hn hx₀ hx₁
  linarith

end ExactQuantumFactoring.RepeatedTrials


end

end OAI
