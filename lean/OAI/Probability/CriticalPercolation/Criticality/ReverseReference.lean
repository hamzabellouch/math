import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.MarkedEntropy

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*} [Fintype M]

noncomputable def weight (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) :
    (n : ℕ) → X → (Fin n → M) → ℝ
  | 0, _, _ => 1
  | n+1, x, m => k n x (m (Fin.last n)) *
    weight k u n (u n x (m (Fin.last n))) (Fin.init m)

def recover (u : ℕ → X → M → X) : (n : ℕ) → X → (Fin n → M) → X
  | 0, x, _ => x
  | n+1, x, m => recover u n (u n x (m (Fin.last n))) (Fin.init m)

omit [Fintype M] in
lemma weight_nonneg (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (n : ℕ) (x : X) (m : Fin n → M) :
    0 ≤ weight k u n x m := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hk _ _ _) (ih _ _)

lemma weight_sum_le (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (n : ℕ) (x : X) : ∑ m, weight k u n x m ≤ 1 := by
  classical
  induction n generalizing x with
  | zero => simp [weight]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => M)).sum_comp]
    simp only [Fin.snocEquiv,Equiv.coe_fn_mk,weight,Fin.snoc_last,Fin.init_snoc,Fintype.sum_prod_type]
    calc
      _ = ∑ m, k n x m * ∑ h, weight k u n (u n x m) h := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ m, k n x m := Finset.sum_le_sum fun m _ => by
        simpa using mul_le_mul_of_nonneg_left (ih (u n x m)) (hk n x m)
      _ ≤ 1 := hs n x

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

noncomputable def terminalWeight (a : I → X → M → ℝ) (x : X) (m : I → M) : ℝ :=
  ∏ i, a i x (m i)

omit [Fintype M] [Fintype X] in
lemma terminalWeight_nonneg (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m)
    (x : X) (m : I → M) : 0 ≤ terminalWeight a x m :=
  Finset.prod_nonneg fun i _ => ha i x (m i)

omit [Fintype X] in
lemma terminalWeight_sum (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1)
    (x : X) : ∑ m, terminalWeight a x m = 1 := by
  unfold terminalWeight
  rw [← Fintype.prod_sum]
  simp only [ha,Finset.prod_const_one]

noncomputable def joint (μ : X → ℝ) (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (a : I → X → M → ℝ) (n : ℕ) (z : X × (Fin n → M) × (I → M)) : ℝ :=
  μ z.1 * weight k u n z.1 z.2.1 * terminalWeight a (recover u n z.1 z.2.1) z.2.2

omit [Fintype M] [Fintype X] in
lemma joint_nonneg (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m) (n : ℕ) (z) :
    0 ≤ joint μ k u a n z :=
  mul_nonneg (mul_nonneg (hμ _) (weight_nonneg k u hk _ _ _)) (terminalWeight_nonneg a ha _ _)

lemma joint_marginal_le (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1) (n : ℕ) (x : X) :
    FiniteEntropy.pushMass Prod.fst (joint μ k u a n) x ≤ μ x := by
  rw [FiniteEntropy.pushMass_fst,Fintype.sum_prod_type]
  simp only [joint,← Finset.mul_sum,terminalWeight_sum a ha,mul_one]
  exact (mul_le_mul_of_nonneg_left (weight_sum_le k u hk hs n x) (hμ x)).trans_eq (mul_one _)

end Terminal
end CriticalPercolation.ReverseReference

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Y] [Fintype Z] in
lemma pushMass_at_supported_injection (P : X → ℝ) (e : X → Y)
    (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (x : X) (hx : P x ≠ 0) : pushMass e P (e x) = P x := by
  unfold pushMass
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    split_ifs with he
    · by_contra hz
      exact hy (hi y x hz hx he)
    · rfl
  · simp

omit [Fintype Z] in
lemma divergence_reference_mono (P R S : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 < P x → 0 < R x) (hRS : ∀ x, R x ≤ S x) :
    divergence P S ≤ divergence P R := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    have hr := hR x hp
    have hs : 0 < S x := hr.trans_le (hRS x)
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hp hs) (div_le_div_of_nonneg_left hp.le hr (hRS x))) (hP x)

theorem mapped_entropy_le (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (e : X → Z) (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (f : Z → Y) (R : Z → ℝ) (hR : ∀ z, 0 ≤ R z) (μ : Y → ℝ)
    (hμ : ∀ y, pushMass f R y ≤ μ y) (cost : X → ℝ)
    (hd : ∀ x, P x ≤ R (e x) * Real.exp (cost x)) :
    divergence (pushMass (f ∘ e) P) μ ≤ ∑ x, P x * cost x := by
  have hs (x : X) (hx : 0 < P x) : 0 < R (e x) := by
    have he := (hx.trans_le (hd x))
    exact (mul_pos_iff.mp he).resolve_right (fun h => (Real.exp_pos _).not_ge h.2.le) |>.1
  have hs' (z : Z) (hz : 0 < pushMass e P z) : 0 < R z := by
    by_contra! hn
    have ht : pushMass e P z ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro x _
      split_ifs with he
      · by_contra! hp
        exact (hs x hp).not_ge (he ▸ hn)
      · rfl
    linarith
  have hs'' (y : Y) (hy : 0 < pushMass f (pushMass e P) y) : 0 < pushMass f R y := by
    by_contra! hn
    have ht : pushMass f (pushMass e P) y ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro z _
      split_ifs with he
      · by_contra! hp
        have hz := (hs' z hp).trans_le (le_pushMass f R hR z)
        rw [he] at hz
        exact hz.not_ge hn
      · rfl
    linarith
  calc
    _ = divergence (pushMass f (pushMass e P)) μ := by rw [pushMass_comp]
    _ ≤ divergence (pushMass f (pushMass e P)) (pushMass f R) :=
      divergence_reference_mono _ _ _ (pushMass_nonneg _ _ (pushMass_nonneg _ _ hP)) hs'' hμ
    _ ≤ divergence (pushMass e P) R := divergence_pushMass_le f _ R
      (pushMass_nonneg _ _ hP) hR hs'
    _ ≤ _ := by
      rw [divergence_pushMass_eq]
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : P x = 0
      · simp [hx]
      · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
        rw [pushMass_at_supported_injection P e hi x hx]
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have hr := hs x hp
        apply (Real.log_le_iff_le_exp (div_pos hp hr)).mpr
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hd x)

end CriticalPercolation.FiniteEntropy
end
end

end OAI
