import OAI.NumberTheory.ShortEgyptian.ReciprocalDifferences

namespace OAI

universe uι uκ uM

namespace ShortEgyptian

open scoped BigOperators
open Finset

@[simp] theorem phase_neg (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

theorem phase_sum_second_derivative_sqrt (f : ℕ → ℝ) (N : ℕ) {lam A : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ A * lam) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by
  have hs := phase_sum_second_derivative f N hlam (Real.sqrt_pos.mpr hlam) hstep
  have hsq := Real.sq_sqrt hlam.le
  have hsp := Real.sqrt_pos.mpr hlam
  have hlams : lam ≤ Real.sqrt lam := (Real.le_sqrt hlam.le hlam.le).mpr (by nlinarith)
  have heq : (A * lam * N + 2) * (2 * Real.sqrt lam / lam + 1 / Real.sqrt lam + 3) =
      3 * A * N * Real.sqrt lam + 3 * A * N * lam + 6 / Real.sqrt lam + 6 := by
    have hdiv : 2 * Real.sqrt lam / lam = 2 / Real.sqrt lam := by
      apply (div_eq_div_iff hlam.ne' hsp.ne').mpr
      nlinarith [hsq]
    rw [hdiv]
    field_simp
    nlinarith [congrArg (fun z : ℝ => 3 * A * (N : ℝ) * z) hsq]
  rw [heq] at hs
  have hh := mul_le_mul_of_nonneg_left hlams (show 0 ≤ 3 * A * (N : ℝ) by positivity)
  linarith

theorem matrix_van_der_corput {ι : Type uι} {κ : Type uκ} (S : Finset ι) (H : Finset κ)
    (hH : H.Nonempty) (a : ι → κ → ℂ) (W : ℂ) (E C : ℝ) (hC : 0 ≤ C)
    (hsum : ∀ h ∈ H, (∑ x ∈ S, a x h) = W)
    (henergy : ∀ h ∈ H, (∑ x ∈ S, ‖a x h‖ ^ 2) ≤ E)
    (hcorr : ∀ h ∈ H, ∀ k ∈ H, h ≠ k →
      ‖∑ x ∈ S, a x h * (starRingEnd ℂ) (a x k)‖ ≤ C) :
    ‖W‖ ^ 2 ≤ (S.card : ℝ) / H.card * E + S.card * C := by
  classical
  let F (x : ι) := ∑ h ∈ H, a x h
  have hsum' : (∑ x ∈ S, F x) = (H.card : ℂ) * W := by
    rw [show (∑ x ∈ S, F x) = ∑ h ∈ H, ∑ x ∈ S, a x h from Finset.sum_comm]
    rw [Finset.sum_congr rfl hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hterm (h : κ) (hh : h ∈ H) (k : κ) (hk : k ∈ H) :
      (∑ x ∈ S, (a x h * (starRingEnd ℂ) (a x k)).re) ≤
        (if h = k then E else 0) + C := by
    by_cases heq : h = k
    · subst k
      simp only [ite_true, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      linarith [henergy h hh]
    · rw [ite_eq_right heq, zero_add, ← Complex.re_sum]
      exact (Complex.re_le_norm _).trans (hcorr h hh k hk heq)
  have hE : (∑ x ∈ S, ‖F x‖ ^ 2) ≤ H.card * E + (H.card : ℝ) ^ 2 * C := by
    simp only [F, complex_sum_norm_sq]
    rw [Finset.sum_comm]
    have hex : (∑ h ∈ H, ∑ x ∈ S, ∑ k ∈ H,
        (a x h * (starRingEnd ℂ) (a x k)).re) =
        ∑ h ∈ H, ∑ k ∈ H, ∑ x ∈ S,
        (a x h * (starRingEnd ℂ) (a x k)).re := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    rw [hex]
    calc
      _ ≤ ∑ h ∈ H, ∑ k ∈ H, ((if h = k then E else 0) + C) :=
        sum_le_sum (fun h hh => sum_le_sum (fun k hk => hterm h hh k hk))
      _ = H.card * E + (H.card : ℝ) ^ 2 * C := by
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq, pow_two, mul_assoc]
  have hcs := complex_sum_sq_le S F
  rw [hsum', norm_mul, Complex.norm_natCast, mul_pow] at hcs
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg S.card))
  have heq : (H.card : ℝ) ^ 2 * ((S.card : ℝ) / H.card * E + S.card * C) =
      S.card * (H.card * E + (H.card : ℝ) ^ 2 * C) := by field_simp
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hcard)).mp
  rw [heq]
  exact hbound

theorem supported_interval_sum_shift {M : Type uM} [AddCommMonoid M]
    (a : ℤ → M) (p q L h : ℤ) (hh0 : 0 ≤ h) (hhL : h ≤ L)
    (hsupp : ∀ n, n ∉ Icc p q → a n = 0) :
    (∑ n ∈ Icc (p - L) q, a (n + h)) = ∑ n ∈ Icc p q, a n := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n + h)
  · intro n _ hn
    by_contra hn'
    exact hn (hsupp _ hn')
  · intro n _ _ m _ _ heq
    omega
  · intro m hm hm0
    have hm' := mem_Icc.mp hm
    have hn : m - h ∈ Icc (p - L) q := mem_Icc.mpr ⟨by omega, by omega⟩
    refine ⟨m - h, hn, ?_, by omega⟩
    simpa only [sub_add_cancel] using hm0
  · intros
    rfl

theorem correlation_norm_symm {ι : Type uι} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ x ∈ S, a x * (starRingEnd ℂ) (b x)‖ =
      ‖∑ x ∈ S, b x * (starRingEnd ℂ) (a x)‖ := by
  rw [← Complex.norm_conj (∑ x ∈ S, a x * (starRingEnd ℂ) (b x)), map_sum]
  simp only [map_mul, starRingEnd_self_apply]
  congr 1
  apply sum_congr rfl
  intro x _
  ring

theorem interval_van_der_corput (a : ℤ → ℂ) (p q : ℤ) (hpq : p ≤ q)
    (L : ℕ) (hL : 1 ≤ L) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : ∀ n, n ∉ Icc p q → a n = 0)
    (hnorm : ∀ n ∈ Icc p q, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 1 ≤ h → h < L →
      ‖∑ n ∈ Icc p q, a (n + h) * (starRingEnd ℂ) (a n)‖ ≤ C) :
    ‖∑ n ∈ Icc p q, a n‖ ^ 2 ≤
      (((Icc p q).card : ℝ) + L) / L * (Icc p q).card +
      (((Icc p q).card : ℝ) + L) * C := by
  classical
  let S := Icc (p - (L : ℤ)) q
  let H := Icc (1 : ℤ) L
  have hH : H.Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hL⟩⟩
  have hsum (h : ℤ) (hh : h ∈ H) : (∑ x ∈ S, a (x + h)) = ∑ x ∈ Icc p q, a x :=
    supported_interval_sum_shift a p q L h (le_trans (by norm_num) (mem_Icc.mp hh).1) (mem_Icc.mp hh).2 hsupp
  have henergy (h : ℤ) (hh : h ∈ H) :
      (∑ x ∈ S, ‖a (x + h)‖ ^ 2) ≤ ((Icc p q).card : ℝ) := by
    rw [supported_interval_sum_shift (fun n => ‖a n‖ ^ 2) p q L h
      (le_trans (by norm_num) (mem_Icc.mp hh).1) (mem_Icc.mp hh).2
      (fun n hn => by rw [hsupp n hn]; simp)]
    calc
      _ ≤ ∑ _n ∈ Icc p q, (1 : ℝ) := sum_le_sum (fun n hn => by
        have hh := hnorm n hn
        nlinarith [norm_nonneg (a n)])
      _ = _ := by simp
  have hcorr' (h k : ℤ) (hh : h ∈ H) (hk : k ∈ H) (hkh : k < h) :
      ‖∑ x ∈ S, a (x + h) * (starRingEnd ℂ) (a (x + k))‖ ≤ C := by
    have heq := supported_interval_sum_shift
      (fun n => a (n + (h - k)) * (starRingEnd ℂ) (a n)) p q L k
      (le_trans (by norm_num) (mem_Icc.mp hk).1) (mem_Icc.mp hk).2
      (fun n hn => by rw [hsupp n hn]; simp)
    have heq' : (∑ x ∈ S, a (x + h) * (starRingEnd ℂ) (a (x + k))) =
        ∑ n ∈ Icc p q, a (n + (h - k)) * (starRingEnd ℂ) (a n) := by
      convert heq using 1
      apply sum_congr rfl
      intro x _
      congr 2
      ring
    rw [heq']
    apply hcorr (h - k) (by omega)
    have hh' := mem_Icc.mp hh
    have hk' := mem_Icc.mp hk
    omega
  have hh := matrix_van_der_corput S H hH (fun x h => a (x + h))
    (∑ x ∈ Icc p q, a x) ((Icc p q).card : ℝ) C hC hsum henergy (by
      intro h hh k hk hne
      rcases lt_or_gt_of_ne hne with hhk | hkh
      · rw [correlation_norm_symm]
        exact hcorr' k h hk hh hhk
      · exact hcorr' h k hh hk hkh)
  have hcH : H.card = L := by simp [H, Int.card_Icc]
  have hcS : S.card = (Icc p q).card + L := by
    simp only [S, Int.card_Icc]
    have h1 : 0 ≤ q + 1 - p := by omega
    have h2 : 0 ≤ q + 1 - (p - (L : ℤ)) := by omega
    exact_mod_cast (show (q + 1 - (p - (L : ℤ))).toNat = (q + 1 - p).toNat + L by omega)
  simpa only [hcH, hcS, Nat.cast_add] using hh

end ShortEgyptian

end OAI
