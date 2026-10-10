import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

theorem squarefree_square_decomposition_unique {u v r s : ℕ}
    (hu : 0 < u) (hr : 0 < r) (hv : Squarefree v) (hs : Squarefree s)
    (h : u ^ 2 * v = r ^ 2 * s) : u = r ∧ v = s := by
  have hvs : v = s := by
    apply Nat.eq_of_factorization_eq hv.ne_zero hs.ne_zero
    intro p
    have hf := congrArg (fun n : ℕ => n.factorization p) h
    simp only [Nat.factorization_mul (pow_ne_zero 2 hu.ne') hv.ne_zero,
      Nat.factorization_mul (pow_ne_zero 2 hr.ne') hs.ne_zero,
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
    have hvp := hv.natFactorization_le_one p
    have hsp := hs.natFactorization_le_one p
    omega
  refine ⟨?_, hvs⟩
  rw [hvs] at h
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (mul_right_cancel₀ hs.ne_zero h)

noncomputable def positiveSquarefreeEquiv :
    ({u : ℕ // 0 < u} × {v : ℕ // Squarefree v}) ≃ {n : ℕ // 0 < n} := by
  let F : ({u : ℕ // 0 < u} × {v : ℕ // Squarefree v}) → {n : ℕ // 0 < n} :=
    fun p => ⟨p.1.val ^ 2 * p.2.val, mul_pos (pow_pos p.1.property 2)
      (Nat.pos_of_ne_zero p.2.property.ne_zero)⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q h
    have h' : p.1.val ^ 2 * p.2.val = q.1.val ^ 2 * q.2.val := congrArg Subtype.val h
    have hu := squarefree_square_decomposition_unique p.1.property q.1.property
      p.2.property q.2.property h'
    exact Prod.ext (Subtype.ext hu.1) (Subtype.ext hu.2)
  · intro n
    obtain ⟨v, u, hv, hu, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos n.property
    exact ⟨(⟨u, hu⟩, ⟨v, hsf⟩), Subtype.ext heq⟩

@[simp] theorem positiveSquarefreeEquiv_apply
    (p : {u : ℕ // 0 < u} × {v : ℕ // Squarefree v}) :
    (positiveSquarefreeEquiv p).val = p.1.val ^ 2 * p.2.val := rfl

noncomputable def squarefreeKernel (n : ℕ) : ℕ :=
  if hn : 0 < n then (positiveSquarefreeEquiv.symm ⟨n, hn⟩).2.val else 0

@[simp] theorem squarefreeKernel_zero : squarefreeKernel 0 = 0 := by simp [squarefreeKernel]

theorem squarefreeKernel_sq_mul {u v : ℕ} (hu : 0 < u) (hv : Squarefree v) :
    squarefreeKernel (u ^ 2 * v) = v := by
  have hn : 0 < u ^ 2 * v := mul_pos (pow_pos hu 2) (Nat.pos_of_ne_zero hv.ne_zero)
  rw [squarefreeKernel, dite_eq_left hn]
  have h : (⟨u ^ 2 * v, hn⟩ : {n : ℕ // 0 < n}) =
      positiveSquarefreeEquiv (⟨u, hu⟩, ⟨v, hv⟩) := rfl
  rw [h, positiveSquarefreeEquiv.symm_apply_apply]

theorem tsum_positive_eq_squarefree_pairs (f : ℕ → ℂ) :
    (∑' n : {n : ℕ // 0 < n}, f n.val) =
      ∑' p : {u : ℕ // 0 < u} × {v : ℕ // Squarefree v}, f (p.1.val ^ 2 * p.2.val) := by
  exact (positiveSquarefreeEquiv.tsum_eq (fun n => f n.val)).symm

theorem tsum_positive_eq_tsum_squarefree (f : ℕ → ℂ)
    (hf : Summable (fun n : {n : ℕ // 0 < n} => f n.val)) :
    (∑' n : {n : ℕ // 0 < n}, f n.val) =
      ∑' v : {v : ℕ // Squarefree v}, ∑' u : {u : ℕ // 0 < u}, f (u.val ^ 2 * v.val) := by
  rw [tsum_positive_eq_squarefree_pairs]
  have h : Summable (fun p : {u : ℕ // 0 < u} × {v : ℕ // Squarefree v} =>
      f (p.1.val ^ 2 * p.2.val)) :=
    hf.comp_injective positiveSquarefreeEquiv.injective
  exact h.tsum_prod.trans h.tsum_comm.symm

theorem tsum_positive_kernel_le (f : ℕ → ℂ)
    (hf : Summable (fun n : {n : ℕ // 0 < n} => f n.val)) (K : ℕ) :
    (∑' n : {n : ℕ // 0 < n}, if squarefreeKernel n.val ≤ K then f n.val else 0) =
      ∑' v : {v : ℕ // Squarefree v}, if v.val ≤ K then
        ∑' u : {u : ℕ // 0 < u}, f (u.val ^ 2 * v.val) else 0 := by
  have hs : Summable (fun n : {n : ℕ // 0 < n} =>
      if squarefreeKernel n.val ≤ K then f n.val else 0) := by
    exact (hf.indicator {n : {n : ℕ // 0 < n} | squarefreeKernel n.val ≤ K}).congr
      (fun n => by simp [Set.indicator_apply])
  rw [tsum_positive_eq_tsum_squarefree (fun n => if squarefreeKernel n ≤ K then f n else 0) hs]
  apply tsum_congr
  intro v
  by_cases hv : v.val ≤ K
  · rw [ite_eq_left hv]
    apply tsum_congr
    intro u
    rw [squarefreeKernel_sq_mul u.property v.property, ite_eq_left hv]
  · rw [ite_eq_right hv]
    calc
      _ = ∑' _u : {u : ℕ // 0 < u}, (0 : ℂ) := by
        apply tsum_congr
        intro u
        rw [squarefreeKernel_sq_mul u.property v.property, ite_eq_right hv]
      _ = 0 := tsum_zero

attribute [irreducible] positiveSquarefreeEquiv squarefreeKernel

end Ostmann.QuadraticSieve

end OAI
