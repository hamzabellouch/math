import OAI.Analysis.CircleDomains.Rigidity.IntervalTraceExtension

namespace OAI

/-! Integration by parts on the open domain intervals between finitely many
holes. The two endpoint errors at each constant-filled hole are explicit. -/
open Set Function MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

theorem sum_gap_differences (n : ℕ) (left right : Fin (n + 1) → ℝ) :
    (∑ i, (right i - left i)) = right (Fin.last n) - left 0 +
      ∑ i : Fin n, (right i.castSucc - left i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i => left i.castSucc) (fun i => right i.castSucc)
    rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => right i - left i), h,
      Fin.sum_univ_castSucc (fun i : Fin (n + 1) => right i.castSucc - left i.succ)]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]
    ring

theorem filled_gap_boundary_identity
    (n : ℕ) (a b left right : Fin (n + 1) → ℝ) (value : Fin n → ℝ)
    (ha : a 0 = 0) (hb : b (Fin.last n) = 0) :
    (∑ i, (right i * b i - left i * a i)) +
      (∑ i : Fin n, value i * (a i.succ - b i.castSucc)) =
    ∑ i : Fin n, ((right i.castSucc - value i) * b i.castSucc +
      (value i - left i.succ) * a i.succ) := by
  rw [sum_gap_differences n (fun i => left i * a i) (fun i => right i * b i), ha, hb]
  simp only [mul_zero, sub_self, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem filled_gap_boundary_bound
    (n : ℕ) (a b left right : Fin (n + 1) → ℝ) (value A : Fin n → ℝ) (C : ℝ)
    (ha : a 0 = 0) (hb : b (Fin.last n) = 0) (_hC : 0 ≤ C)
    (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ i, |right i.castSucc - value i| ≤ A i)
    (hright : ∀ i, |value i - left i.succ| ≤ A i)
    (hφleft : ∀ i : Fin n, |b i.castSucc| ≤ C) (hφright : ∀ i : Fin n, |a i.succ| ≤ C) :
    |(∑ i, (right i * b i - left i * a i)) +
      (∑ i : Fin n, value i * (a i.succ - b i.castSucc))| ≤
        2 * C * ∑ i, A i := by
  rw [filled_gap_boundary_identity n a b left right value ha hb]
  calc
    _ ≤ ∑ i : Fin n, |(right i.castSucc - value i) * b i.castSucc +
        (value i - left i.succ) * a i.succ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, 2 * C * A i := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ := mul_le_mul (hleft i) (hφleft i) (abs_nonneg _) (hA i)
      have h₂ := mul_le_mul (hright i) (hφright i) (abs_nonneg _) (hA i)
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul]
      nlinarith
    _ = _ := by rw [Finset.mul_sum]

theorem integration_by_parts_with_filled_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (g : Fin (n + 1) → ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hg : ∀ i, AbsolutelyContinuousOnInterval (g i) (a i) (b i))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ i, |g i.castSucc (b i.castSucc) - value i| ≤ A i)
    (hright : ∀ i, |value i - g i.succ (a i.succ)| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∑ i, ((∫ x in a i..b i, g i x * deriv φ x) +
      (∫ x in a i..b i, deriv (g i) x * φ x))) +
      (∑ i : Fin n, value i * (φ (a i.succ) - φ (b i.castSucc)))| ≤
        2 * C * ∑ i, A i := by
  have he (i : Fin (n + 1)) :
      (∫ x in a i..b i, g i x * deriv φ x) + (∫ x in a i..b i, deriv (g i) x * φ x) =
        g i (b i) * φ (b i) - g i (a i) * φ (a i) := by
    have h := (hg i).integral_mul_deriv_eq_deriv_mul
      hφ.contDiffOn.absolutelyContinuousOnInterval
    linarith
  simp_rw [he]
  exact filled_gap_boundary_bound n (fun i => φ (a i)) (fun i => φ (b i))
    (fun i => g i (a i)) (fun i => g i (b i)) value A C hzero hone hC hA
    hleft hright hφleft hφright

end CircleDomainRigidity

end OAI
