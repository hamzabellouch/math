import Mathlib

namespace OAI

noncomputable section

namespace Problem315.CountEigenvalue

theorem abs_eigenvalue_sub_one_le_one
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : |lam - 1| ≤ 1 := by
  rw [abs_mul, hδ] at hbound
  nlinarith

theorem eigenvalue_le_two
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : lam ≤ 2 := by
  have h := abs_eigenvalue_sub_one_le_one hM hδ hbound
  have := (abs_le.mp h).2
  linarith

theorem fin_eq_zero_value_of_adjacent_eq {m : ℕ} (b : Fin (m + 1) → ℝ)
    (h : ∀ t : Fin m, b t.succ = b t.castSucc) :
    ∀ t, b t = b 0 := by
  intro t
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih => exact (h t).trans ih

theorem exists_nonzero_adjacent_difference {ι : Type*} {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ)
    (hne : ∃ i s t, b i s ≠ b i t) :
    ∃ i, ∃ t : Fin m, b i t.succ - b i t.castSucc ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, s, t, hst⟩ := hne
  have hi : ∀ t : Fin m, b i t.succ = b i t.castSucc := by
    intro t
    exact sub_eq_zero.mp (h i t)
  exact hst ((fin_eq_zero_value_of_adjacent_eq (b i) hi s).trans
    (fin_eq_zero_value_of_adjacent_eq (b i) hi t).symm)

theorem exists_positive_max_abs {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hne : ∃ i, x i ≠ 0) :
    ∃ i, 0 < |x i| ∧ ∀ j, |x j| ≤ |x i| := by
  classical
  obtain ⟨j, hj⟩ := hne
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun k => |x k|) ⟨j, Finset.mem_univ j⟩
  refine ⟨i, lt_of_lt_of_le (abs_pos.mpr hj) (hi j (Finset.mem_univ j)), ?_⟩
  intro k
  exact hi k (Finset.mem_univ k)

theorem eigenvalue_le_two_of_adjacent_coupling
    {ι : Type*} [Fintype ι] {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hne : ∃ i s t, b i s ≠ b i t)
    (hcoupling : ∀ i (t : Fin m),
      (∀ j (s : Fin m),
        |b j s.succ - b j s.castSucc| ≤ |b i t.succ - b i t.castSucc|) →
      |(lam - 1) * (b i t.succ - b i t.castSucc)| ≤
        |b i t.succ - b i t.castSucc|) : lam ≤ 2 := by
  obtain ⟨i, t, hit⟩ := exists_nonzero_adjacent_difference b hne
  let x : ι × Fin m → ℝ := fun p => b p.1 p.2.succ - b p.1 p.2.castSucc
  obtain ⟨⟨j, s⟩, hpos, hmax⟩ := exists_positive_max_abs x ⟨(i, t), hit⟩
  exact eigenvalue_le_two hpos rfl (hcoupling j s (fun k u => hmax (k, u)))

theorem exists_nonconstant_of_centered
    {ι : Type*} {m : ℕ} (b p : ι → Fin (m + 1) → ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t = 0)
    (hne : ∃ i t, b i t ≠ 0) :
    ∃ i s t, b i s ≠ b i t := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i, t, hit⟩ := hne
  have hi : (∑ u, p i u * b i u) = b i t := by
    calc
      _ = ∑ u, p i u * b i t := Finset.sum_congr rfl (fun u _ => by rw [h i u t])
      _ = (∑ u, p i u) * b i t := (Finset.sum_mul _ _ _).symm
      _ = b i t := by rw [hmass, one_mul]
  exact hit (hi.symm.trans (hcenter i))

theorem eigenvalue_le_two_of_centered_adjacent_coupling
    {ι : Type*} [Fintype ι] {m : ℕ}
    (b p : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t = 0)
    (hne : ∃ i t, b i t ≠ 0)
    (hcoupling : ∀ i (t : Fin m),
      (∀ j (s : Fin m),
        |b j s.succ - b j s.castSucc| ≤ |b i t.succ - b i t.castSucc|) →
      |(lam - 1) * (b i t.succ - b i t.castSucc)| ≤
        |b i t.succ - b i t.castSucc|) : lam ≤ 2 := by
  exact eigenvalue_le_two_of_adjacent_coupling b lam
    (exists_nonconstant_of_centered b p hmass hcenter hne) hcoupling

end Problem315.CountEigenvalue

end

end OAI
