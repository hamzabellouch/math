import OAI.Analysis.Laughlin.Tensor.PairContraction

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pair_update_insert {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (u v x y : Fin (Q+1)) (b : Configuration n Q) :
    Function.update (Function.update (i.insertNth u (j.insertNth v b) : Configuration (n+2) Q) i x)
      (i.succAbove j) y = i.insertNth x (j.insertNth y b) := by
  rw [Fin.update_insertNth, ← Fin.insertNth_update, Fin.update_insertNth]

theorem pairAmplitude_insert {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (p : ℕ)
    (u v : Fin (Q+1)) (b : Configuration n Q) :
    pairAmplitude ψ i (i.succAbove j) p (i.insertNth u (j.insertNth v b)) =
      ((-1 : ℂ)^i.val * (-1 : ℂ)^j.val) * headPairAmplitude ψ p b := by
  simp only [pairAmplitude,pair_update_insert,antisymmetric_insertNth hψ]
  have he (x y : Fin (Q+1)) :
      ψ (Fin.cons x (j.insertNth y b)) =
        (-1 : ℂ)^j.val * ψ (Fin.cons x (Fin.cons y b)) :=
    antisymmetric_insertNth (antisymmetric_cons hψ x) j y b
  simp only [he,headPairAmplitude,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem anchored_pair_sum {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (p : ℕ) :
    (∑ a : Configuration (n+2) Q,
      if a i = 0 ∧ a (i.succAbove j) = 0 then
        ‖pairAmplitude ψ i (i.succAbove j) p a‖^2 else 0) =
      ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
  rw [sum_config_insert i]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  simp_rw [sum_config_insert j]
  simp only [Fin.insertNth_apply_same,pairAmplitude_insert ψ hψ]
  simp [norm_pow,ite_and]

theorem unordered_position_count (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) =
      (n : ℝ)*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ,Fin.lt_def,Fin.val_zero,Fin.val_succ,
      Nat.zero_lt_succ,Nat.not_lt_zero,ite_true,ite_false,Nat.add_lt_add_iff_right]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      zero_add]
    change (n : ℝ) + (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) = _
    rw [ih]
    push_cast
    ring

theorem energy_head_pair (n Q : ℕ) (ψ : State (n+2) Q) (hψ : Antisymmetric ψ) :
    energy ψ = ((n+2 : ℝ)*(n+1)/2) *
      ∑ p ∈ Finset.range (2*Q-1), ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
  have he (i j : Fin (n+2)) (hij : i < j) (p : ℕ) :
      (∑ a : Configuration (n+2) Q,
        if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖^2 else 0) =
        ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
    obtain ⟨k,hk⟩ := (Fin.exists_succAbove_eq (ne_of_lt hij).symm)
    subst j
    exact anchored_pair_sum ψ hψ i k p
  unfold energy
  have hs : (∑ i : Fin (n+2), ∑ j : Fin (n+2), if i < j then (1 : ℝ) else 0) =
      (n+2 : ℝ)*(n+1)/2 := by
    rw [unordered_position_count]
    push_cast
    ring
  rw [← hs,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [ite_eq_left hij,one_mul]
    exact Finset.sum_congr rfl (fun p hp => he i j hij p)
  · simp [hij]

end Laughlin

end OAI
