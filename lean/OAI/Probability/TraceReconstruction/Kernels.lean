import OAI.Probability.TraceReconstruction.Binomial

namespace OAI

/-!
# Kernels

Constrained rank-gap sums, correlated anchor kernels, window kernels, lattice Laplace sums, and geometric degree bounds.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

/-- Eliminate one output gap by its prescribed total before dropping the
other rank constraints. This is the exact finite summation step used in
the conditional rank-kernel estimate. -/
theorem constrained_sum_product_le (r L : ℕ)
    (f : Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf : ∀ i k, 0 ≤ f i k) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k, f 0 k ≤ M) :
    (∑ z : Fin (r + 1) → Fin (L + 1),
      if ∑ j, (z j).val = L then ∏ j, f j (z j) else 0) ≤
        M * ∏ i : Fin r, ∑ k, f i.succ k := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin (L + 1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hpoint (z : Fin r → Fin (L + 1)) :
      (∑ k : Fin (L + 1),
        if k.val + ∑ i, (z i).val = L then f 0 k * ∏ i, f i.succ (z i) else 0) ≤
          M * ∏ i, f i.succ (z i) := by
    by_cases hz : ∑ i, (z i).val ≤ L
    · let k₀ : Fin (L + 1) := ⟨L - ∑ i, (z i).val, by omega⟩
      have heq (k : Fin (L + 1)) : k.val + ∑ i, (z i).val = L ↔ k = k₀ := by
        change _ ↔ k = ⟨L - ∑ i, (z i).val, _⟩
        rw [Fin.ext_iff]
        simp only
        omega
      simp_rw [heq]
      rw [Fintype.sum_ite_eq']
      exact mul_le_mul_of_nonneg_right (hbound k₀) (Finset.prod_nonneg fun i _ => hf _ _)
    · have heq (k : Fin (L + 1)) : ¬ (k.val + ∑ i, (z i).val = L) := by omega
      simp_rw [ite_eq_right (heq _), Finset.sum_const_zero]
      exact mul_nonneg hM (Finset.prod_nonneg fun i _ => hf _ _)
  calc
    _ ≤ ∑ z : Fin r → Fin (L + 1), M * ∏ i, f i.succ (z i) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using hpoint z
    _ = _ := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (i : Fin r) (k : Fin (L + 1)) => f i.succ k)]

/-- The product of two rank kernels has one scalar denominator factor,
one uniform gap factor and independent one-dimensional cross-overlaps. -/
theorem constrained_cross_kernel_le (r L : ℕ)
    (f g : Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf : ∀ i k, 0 ≤ f i k) (hg : ∀ i k, 0 ≤ g i k)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ k, f 0 k * g 0 k ≤ M) :
    (∑ z : Fin (r + 1) → Fin (L + 1),
      if ∑ j, (z j).val = L then (∏ j, f j (z j)) * (∏ j, g j (z j)) else 0) ≤
        M * ∏ i : Fin r, ∑ k, f i.succ k * g i.succ k := by
  simp_rw [← Finset.prod_mul_distrib]
  exact constrained_sum_product_le r L (fun i k => f i k * g i k)
    (fun i k => mul_nonneg (hf i k) (hg i k)) M hM hbound

end TraceReconstruction

namespace TraceReconstruction

/-! ## Correlated sibling-anchor estimate

This is the analytic summation step in the correlated-anchor estimate, subsection
“Summing the correlated anchor kernels”. The common latent draw is kept
inside the joint kernel, so independence of the two displaced locations
is NOT assumed. Conditional independence only factors the two local
kernels for each fixed common draw. All arrays here have finite support;
the integer-jitter application uses a finite interval containing that support.
-/

section CorrelatedAnchors

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]

/-- Mixture of conditional products; `p` is the common displacement law. -/
def jointKernel (p : Ω → ℝ) (a : Ω → I → ℝ) (b : Ω → J → ℝ)
    (i : I) (j : J) : ℝ := ∑ w, p w * a w i * b w j

omit [Fintype I] [Fintype J] in
theorem jointKernel_nonneg
    (p : Ω → ℝ) (a : Ω → I → ℝ) (b : Ω → J → ℝ)
    (hp : ∀ w, 0 ≤ p w) (ha : ∀ w i, 0 ≤ a w i)
    (hb : ∀ w j, 0 ≤ b w j) (i : I) (j : J) :
    0 ≤ jointKernel p a b i j := by
  exact Finset.sum_nonneg fun w _ => mul_nonneg (mul_nonneg (hp w) (ha w i)) (hb w j)

theorem sum_jointKernel
    (p : Ω → ℝ) (a : Ω → I → ℝ) (b : Ω → J → ℝ) (L M : ℝ)
    (hp : ∑ w, p w = 1)
    (ha : ∀ w, ∑ i, a w i = L) (hb : ∀ w, ∑ j, b w j = M) :
    ∑ i, ∑ j, jointKernel p a b i j = L * M := by
  simp only [jointKernel]
  have hcomm (i : I) :
      (∑ j : J, ∑ w : Ω, p w * a w i * b w j) =
        ∑ w : Ω, ∑ j : J, p w * a w i * b w j := Finset.sum_comm
  simp_rw [hcomm]
  simp_rw [← Finset.mul_sum, hb]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha]
  rw [← Finset.sum_mul, hp, one_mul]

omit [Fintype I] [Fintype J] in
theorem jointKernel_le
    (p : Ω → ℝ) (a : Ω → I → ℝ) (b : Ω → J → ℝ) (A B : ℝ)
    (hp : ∀ w, 0 ≤ p w) (ha : ∀ w i, 0 ≤ a w i)
    (hB : 0 ≤ B) (hb : ∀ w j, b w j ≤ B)
    (hA : ∀ i, ∑ w, p w * a w i ≤ A) (i : I) (j : J) :
    jointKernel p a b i j ≤ A * B := by
  calc
    jointKernel p a b i j ≤ ∑ w, (p w * a w i) * B := by
      exact Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (hb w j) (mul_nonneg (hp w) (ha w i))
    _ = (∑ w, p w * a w i) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ A * B := mul_le_mul_of_nonneg_right (hA i) hB

/-- The joint squared-sum estimate retaining the common jitter. In the
    manuscript A=L/(omega*sqrt(T*t)) and B=M/(omega*sqrt(t)),
    up to the explicit absolute binomial constants. -/
theorem correlated_anchor_square_sum
    (p : Ω → ℝ) (a : Ω → I → ℝ) (b : Ω → J → ℝ)
    (L M A B : ℝ)
    (hp0 : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1)
    (ha0 : ∀ w i, 0 ≤ a w i) (hb0 : ∀ w j, 0 ≤ b w j)
    (ha1 : ∀ w, ∑ i, a w i = L) (hb1 : ∀ w, ∑ j, b w j = M)
    (hB : 0 ≤ B) (hb : ∀ w j, b w j ≤ B)
    (hA : ∀ i, ∑ w, p w * a w i ≤ A) :
    ∑ i, ∑ j, (jointKernel p a b i j) ^ 2 ≤ (A * B) * (L * M) := by
  calc
    ∑ i, ∑ j, (jointKernel p a b i j) ^ 2 ≤
        ∑ i, ∑ j, (A * B) * jointKernel p a b i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h0 := jointKernel_nonneg p a b hp0 ha0 hb0 i j
      have h1 := jointKernel_le p a b A B hp0 ha0 hB hb hA i j
      nlinarith
    _ = (A * B) * (∑ i, ∑ j, jointKernel p a b i j) := by
      simp_rw [← Finset.mul_sum]
    _ = (A * B) * (L * M) := by rw [sum_jointKernel p a b L M hp1 ha1 hb1]

end CorrelatedAnchors


end TraceReconstruction

namespace TraceReconstruction

/-- Truncating output ranks cannot increase a binomial cross-overlap. -/
theorem binomial_overlap_truncate (g h L : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) :
    (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤
      ∑ k ∈ Finset.range (h + 1), binomialMass g p k * binomialMass h p k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => binomialMass g p k * binomialMass h p k) (L + 1)]
  by_cases hL : L ≤ h
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    exact mul_nonneg (binomialMass_nonneg g k hp) (binomialMass_nonneg h k hp)
  · apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hhk : h < k := by
      simp only [Finset.mem_range, not_lt] at hk
      omega
    simp [binomialMass, Nat.choose_eq_zero_of_lt hhk]

/-- Gaussian cross-overlap with the prefactor attached to either prescribed
first length, removing the order restriction in the tilting proof. -/
theorem binomial_gaussian_overlap_general (g h L : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hS : 0 < g + h) :
    (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤
      Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) *
        Real.exp (-((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h))) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  by_cases hhg : h ≤ g
  · exact (binomial_overlap_truncate g h L ⟨hp0.le, hp.2.le⟩).trans
      (binomial_gaussian_overlap g h hp hhg hS)
  · have hgh : g ≤ h := by omega
    have ho := (binomial_overlap_truncate h g L ⟨hp0.le, hp.2.le⟩).trans
      (binomial_gaussian_overlap h g hp hgh (by omega))
    have hb : Real.sqrt (2 / (((h : ℝ) + 1) * p * (1 - p))) ≤
        Real.sqrt (2 / (((g : ℝ) + 1) * p * (1 - p))) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by norm_num)
        (by nlinarith only [mul_pos (show (0 : ℝ) < (g : ℝ) + 1 by positivity) hpq])
      have hcast : (g : ℝ) ≤ h := by exact_mod_cast hgh
      have ht := mul_le_mul_of_nonneg_right (show (g : ℝ) + 1 ≤ (h : ℝ) + 1 by linarith) hpq.le
      nlinarith only [ht]
    have heq : -((h : ℝ) - g) ^ 2 / (16 * ((h : ℝ) + g)) =
        -((g : ℝ) - h) ^ 2 / (16 * ((g : ℝ) + h)) := by ring
    rw [heq] at ho
    exact (by simpa only [mul_comm] using ho :
      (∑ k : Fin (L + 1), binomialMass g p k * binomialMass h p k) ≤ _).trans
        (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _))

/-- The exact conditional rank kernel, including the fixed count
normalization, before any coarse-gap estimates or restrictions. -/
def rankKernel (r n l : ℕ) (p : ℝ) (g : Fin (r + 1) → ℕ)
    (z : Fin (r + 1) → Fin (l + 1)) : ℝ :=
  if r ≤ l ∧ ∑ j, (z j).val = l - r then
    p ^ r / binomialMass n p l * ∏ j, binomialMass (g j) p (z j) else 0

/-- Largest-gap elimination for the conditional rank kernel. The displayed
constant is absolute; no asymptotic proposal or Stirling theorem is assumed. -/
theorem rankKernel_cross_le (r n l : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ico (1 / 2 : ℝ) 1) (hl : l ≤ n)
    (hmean : (n : ℝ) * p = l) (hv : 1 ≤ (n : ℝ) * p * (1 - p))
    (g h : Fin (r + 1) → ℕ) :
    (∑ z : Fin (r + 1) → Fin (l - r + 1),
      if ∑ j, (z j).val = l - r then
        (p ^ r / binomialMass n p l) ^ 2 *
          (∏ j, binomialMass (g j) p (z j)) *
          (∏ j, binomialMass (h j) p (z j)) else 0) ≤
      (4608 * n / ((g 0 : ℝ) + 1)) *
        ∏ i : Fin r, ∑ k : Fin (l - r + 1),
          binomialMass (g i.succ) p k * binomialMass (h i.succ) p k := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp.2)
  have hden : 0 < ((g 0 : ℝ) + 1) * p * (1 - p) := by
    nlinarith only [mul_pos (show (0 : ℝ) < (g 0 : ℝ) + 1 by positivity) hpq]
  have hc : (p ^ r / binomialMass n p l) ^ 2 ≤ 144 * ((n : ℝ) * p * (1 - p)) := by
    rw [div_eq_mul_inv, mul_pow]
    apply (mul_le_mul_of_nonneg_right
      (show (p ^ r) ^ 2 ≤ (1 : ℝ) by
        exact pow_le_one₀ (pow_nonneg hp0.le _) (pow_le_one₀ hp0.le hp.2.le))
      (sq_nonneg _)).trans
    simpa only [one_mul] using binomialMass_mean_inverse_sq n l ⟨hp0, hp.2⟩ hl hmean hv
  have hx := constrained_cross_kernel_le r (l - r)
    (fun i k => binomialMass (g i) p k) (fun i k => binomialMass (h i) p k)
    (fun i k => binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩)
    (fun i k => binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩)
    (32 / (((g 0 : ℝ) + 1) * p * (1 - p))) (by positivity)
    (fun k => binomial_product_sup (g 0) (h 0) k hp)
  have hprod : 0 ≤ ∏ i : Fin r, ∑ k : Fin (l - r + 1),
      binomialMass (g i.succ) p k * binomialMass (h i.succ) p k := by
    apply Finset.prod_nonneg
    intro i _
    exact Finset.sum_nonneg fun k _ => mul_nonneg
      (binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩)
      (binomialMass_nonneg _ _ ⟨hp0.le, hp.2.le⟩)
  calc
    _ = (p ^ r / binomialMass n p l) ^ 2 *
      (∑ z : Fin (r + 1) → Fin (l - r + 1),
        if ∑ j, (z j).val = l - r then
          (∏ j, binomialMass (g j) p (z j)) *
          (∏ j, binomialMass (h j) p (z j)) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> ring
    _ ≤ (p ^ r / binomialMass n p l) ^ 2 *
      ((32 / (((g 0 : ℝ) + 1) * p * (1 - p))) * _) :=
      mul_le_mul_of_nonneg_left hx (sq_nonneg _)
    _ ≤ (144 * ((n : ℝ) * p * (1 - p))) *
      ((32 / (((g 0 : ℝ) + 1) * p * (1 - p))) * _) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) hprod)
    _ = _ := by
      have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
      field_simp
      ring

end TraceReconstruction

namespace TraceReconstruction
theorem fairSeries_total (n : ℕ) : ∑' z : ℤ, (fairSeries n).coeff z = 1 := by
  have h := fairSeries_L1 n
  unfold seriesL1 at h
  simpa only [abs_of_nonneg (fairSeries_nonneg n _)] using h

theorem fairSeries_sum_finite_le_one (n : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, (fairSeries n).coeff (c-z) ≤ 1 := by
  have hs : Summable (fun z : ℤ => (fairSeries n).coeff (c-z)) := by
    exact (Equiv.subLeft c).summable_iff.mpr (series_summable (fairSeries n) id rfl)
  have hh : (∑' z : ℤ, (fairSeries n).coeff (c-z)) = 1 := by
    simpa using ((Equiv.subLeft c).tsum_eq (fun z => (fairSeries n).coeff z)).trans
      (fairSeries_total n)
  rw [← hh]
  exact Summable.sum_le_tsum A (fun _ _ => fairSeries_nonneg n _) hs

def windowKernel (n L : ℕ) (z : ℤ) : ℝ :=
  ∑ a ∈ Finset.range L, (fairSeries n).coeff ((a:ℤ)-z)

theorem windowKernel_nonneg (n L : ℕ) (z : ℤ) : 0 ≤ windowKernel n L z :=
  Finset.sum_nonneg (fun _ _ => fairSeries_nonneg n _)

theorem windowKernel_sup (n L : ℕ) (z : ℤ) :
    windowKernel n L z ≤ L*binomialBound n := by
  calc
    _ ≤ ∑ _a ∈ Finset.range L, binomialBound n := by
      apply Finset.sum_le_sum
      intro a _
      exact (le_abs_self _).trans (fairSeries_coeff_bound n _)
    _ = _ := by simp

theorem windowKernel_sum (n L : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, windowKernel n L (z-c) ≤ L := by
  unfold windowKernel
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _a ∈ Finset.range L, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [show ∀ z : ℤ, (a:ℤ)-(z-c)=(a:ℤ)+c-z from fun z => by omega]
        using fairSeries_sum_finite_le_one n A ((a:ℤ)+c)
    _ = _ := by simp

theorem windowKernel_energy (n L : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, windowKernel n L (z-c)^2 ≤ L^2*binomialBound n := by
  calc
    _ ≤ ∑ z ∈ A, windowKernel n L (z-c)*(L*binomialBound n) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left
        (windowKernel_sup n L (z-c)) (windowKernel_nonneg n L (z-c))
    _ = (∑ z ∈ A, windowKernel n L (z-c))*(L*binomialBound n) := by rw [Finset.sum_mul]
    _ ≤ L*(L*binomialBound n) := mul_le_mul_of_nonneg_right
      (windowKernel_sum n L A c) (by positivity [binomialBound_nonneg n])
    _ = _ := by ring

def jointWindowKernel (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) : ℝ :=
  ∑ v ∈ (fairSeries g).coeff.support,
    (fairSeries g).coeff v * windowKernel n₁ L (z₁+v) * windowKernel n₂ L (z₂+v)

theorem windowKernel_average (g n L : ℕ) (z : ℤ) :
    (∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v * windowKernel n L (z+v)) =
      windowKernel (g+n) L z := by
  unfold windowKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [fairSeries_add, AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  omega

theorem jointWindowKernel_nonneg (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) :
    0 ≤ jointWindowKernel g n₁ n₂ L z₁ z₂ := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (mul_nonneg (fairSeries_nonneg g v) (windowKernel_nonneg n₁ L _))
    (windowKernel_nonneg n₂ L _)

theorem jointWindowKernel_sup (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) :
    jointWindowKernel g n₁ n₂ L z₁ z₂ ≤ L^2*binomialBound g*binomialBound n₂ := by
  have hbound : binomialBound (g+n₁) ≤ binomialBound g := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    simp only [Nat.cast_add]; linarith [show (0:ℝ) ≤ n₁ by positivity]
  calc
    _ ≤ ∑ v ∈ (fairSeries g).coeff.support,
        (fairSeries g).coeff v * windowKernel n₁ L (z₁+v) * (L*binomialBound n₂) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (windowKernel_sup n₂ L _) (mul_nonneg
        (fairSeries_nonneg g v) (windowKernel_nonneg n₁ L _))
    _ = windowKernel (g+n₁) L z₁ * (L*binomialBound n₂) := by
      rw [← Finset.sum_mul, windowKernel_average]
    _ ≤ (L*binomialBound g)*(L*binomialBound n₂) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (binomialBound_nonneg n₂))
      exact (windowKernel_sup (g+n₁) L z₁).trans
        (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ = _ := by ring

theorem jointWindowKernel_sum (g n₁ n₂ L : ℕ) (A B : Finset ℤ) (c₁ c₂ : ℤ) :
    ∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂) ≤ L^2 := by
  unfold jointWindowKernel
  simp_rw [Finset.sum_comm (s := B)]
  rw [Finset.sum_comm]
  calc
    _ = ∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v *
        (∑ z₁ ∈ A, windowKernel n₁ L ((z₁-c₁)+v)) *
        (∑ z₂ ∈ B, windowKernel n₂ L ((z₂-c₂)+v)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v * (L*L) := by
      apply Finset.sum_le_sum
      intro v _
      have h1 : (∑ z₁ ∈ A, windowKernel n₁ L ((z₁-c₁)+v)) ≤ L := by
        simpa only [show ∀ z : ℤ, (z-c₁)+v = z-(c₁-v) from fun z => by omega]
          using windowKernel_sum n₁ L A (c₁-v)
      have h2 : (∑ z₂ ∈ B, windowKernel n₂ L ((z₂-c₂)+v)) ≤ L := by
        simpa only [show ∀ z : ℤ, (z-c₂)+v = z-(c₂-v) from fun z => by omega]
          using windowKernel_sum n₂ L B (c₂-v)
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (fairSeries_nonneg g v)
      exact mul_le_mul h1 h2 (Finset.sum_nonneg (fun z _ => windowKernel_nonneg n₂ L _)) (by positivity)
    _ = L^2 := by
      rw [← Finset.sum_mul]
      have ht : (∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v) = 1 := by
        have h := fairSeries_L1 g
        rw [seriesL1_eq_sum] at h
        simpa only [abs_of_nonneg (fairSeries_nonneg g _)] using h
      rw [ht]; ring

theorem jointWindowKernel_energy (g n₁ n₂ L : ℕ) (A B : Finset ℤ) (c₁ c₂ : ℤ) :
    ∑ z₁ ∈ A, ∑ z₂ ∈ B, (jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂))^2 ≤
      L^4*binomialBound g*binomialBound n₂ := by
  calc
    _ ≤ ∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂) *
        (L^2*binomialBound g*binomialBound n₂) := by
      apply Finset.sum_le_sum
      intro z₁ _
      apply Finset.sum_le_sum
      intro z₂ _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left
        (jointWindowKernel_sup g n₁ n₂ L _ _) (jointWindowKernel_nonneg g n₁ n₂ L _ _)
    _ = (∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂)) *
        (L^2*binomialBound g*binomialBound n₂) := by simp_rw [Finset.sum_mul]
    _ ≤ L^2*(L^2*binomialBound g*binomialBound n₂) := mul_le_mul_of_nonneg_right
      (jointWindowKernel_sum g n₁ n₂ L A B c₁ c₂)
      (mul_nonneg (mul_nonneg (by positivity) (binomialBound_nonneg g)) (binomialBound_nonneg n₂))
    _ = _ := by ring
end TraceReconstruction

open Filter
open scoped Topology


namespace TraceReconstruction

/-- Elementary discrete integral comparison, including the singular first cell. -/
theorem sum_inverse_sqrt (N : ℕ) :
    (∑ k ∈ Finset.range N, (Real.sqrt (k+1:ℝ))⁻¹) ≤ 2*Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ (N:ℝ) := by positivity
    have hp : 0 < Real.sqrt (N+1:ℝ) := Real.sqrt_pos.2 (by positivity)
    have hs : Real.sqrt (N:ℝ) ≤ Real.sqrt (N+1:ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h1 := Real.sq_sqrt hn
    have h2 := Real.sq_sqrt (show 0 ≤ (N+1:ℝ) by positivity)
    have hstep : (Real.sqrt (N+1:ℝ))⁻¹ ≤ 2*(Real.sqrt (N+1:ℝ)-Real.sqrt N) := by
      apply (inv_le_iff_one_le_mul₀ hp).2
      nlinarith [sq_nonneg (Real.sqrt (N+1:ℝ)-Real.sqrt N)]
    push_cast
    linarith

theorem exp_gap_lower {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    h/2 ≤ 1-Real.exp (-h) := by
  have he := Real.add_one_le_exp h
  have hp : 0 < Real.exp h := Real.exp_pos h
  have hp' : 0 < 1+h := by linarith
  have hinv : (Real.exp h)⁻¹ ≤ (1+h)⁻¹ := inv_anti₀ hp' (by simpa [add_comm] using he)
  rw [Real.exp_neg]
  have hi : (1+h)⁻¹*(1+h)=1 := inv_mul_cancel₀ (ne_of_gt hp')
  nlinarith [mul_nonneg hh.le (sub_nonneg.mpr h1)]

theorem sum_exp_decay {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (M : ℕ) :
    (∑ k ∈ Finset.range M, Real.exp (-h*(k:ℝ))) ≤ 2/h := by
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hf : (∑ k ∈ Finset.range M, (Real.exp (-h))^k) ≤ (1-Real.exp (-h))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1-Real.exp (-h)), geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg he M)
  have hi : (1-Real.exp (-h))⁻¹ ≤ 2/h := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0<1-Real.exp (-h))]
    have hb := exp_gap_lower hh h1
    have := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2/h by positivity)
    nlinarith [div_mul_cancel₀ (2:ℝ) hh.ne']
  calc
    _ = ∑ k ∈ Finset.range M, (Real.exp (-h))^k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := hf.trans hi

/-- The uniform lattice Laplace estimate used by the initial-pair construction, with an absolute constant. -/
theorem coarse_laplace_sum {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (M : ℕ) :
    (∑ k ∈ Finset.range M, (Real.sqrt (k+1:ℝ))⁻¹ *
      Real.exp (-h*(k+1:ℝ))) ≤ 6/Real.sqrt h := by
  let N := ⌈1/h⌉₊
  have hN : 1/h ≤ (N:ℝ) := Nat.le_ceil _
  have hNup : (N:ℝ) < 1/h+1 := Nat.ceil_lt_add_one (by positivity)
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hNsqrt : Real.sqrt N ≤ 2/Real.sqrt h := by
    have hn : (N:ℝ)*h ≤ 2 := by
      have hx := mul_le_mul_of_nonneg_right hNup.le hh.le
      have hc : (1/h)*h=1 := div_mul_cancel₀ _ hh.ne'
      nlinarith
    have hprod : Real.sqrt N * Real.sqrt h ≤ 2 := by
      have hsqh := Real.sq_sqrt hh.le
      have hsqN := Real.sq_sqrt (show 0≤(N:ℝ) by positivity)
      have hnon : 0≤Real.sqrt N*Real.sqrt h := by positivity
      nlinarith [sq_nonneg (Real.sqrt N*Real.sqrt h)]
    exact (le_div_iff₀ hs).2 hprod
  let low := (Finset.range M).filter (fun k => k<N)
  let high := (Finset.range M).filter (fun k => ¬k<N)
  have hlo : (∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) ≤
      2*Real.sqrt N := by
    calc
      _ ≤ ∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [show (0:ℝ)≤k by positivity]))
      _ ≤ ∑ k ∈ Finset.range N, (Real.sqrt (k+1:ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
        · intros; positivity
      _ ≤ _ := sum_inverse_sqrt N
  have hhi : (∑ k ∈ high, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) ≤
      Real.sqrt h * (2/h) := by
    calc
      _ ≤ ∑ k ∈ high, Real.sqrt h * Real.exp (-h*(k:ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : N ≤ k := Nat.le_of_not_gt (Finset.mem_filter.mp hk).2
        have hkR : 1/h ≤ (k+1:ℝ) := hN.trans (by exact_mod_cast (by omega : N≤k+1))
        have hinv : (Real.sqrt (k+1:ℝ))⁻¹ ≤ Real.sqrt h := by
          apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 (by positivity))).2
          have hmul : 1 ≤ h*(k+1:ℝ) := by simpa [mul_comm] using (div_le_iff₀ hh).mp hkR
          have hsqh := Real.sq_sqrt hh.le
          have hsqk := Real.sq_sqrt (show 0≤(k+1:ℝ) by positivity)
          nlinarith [mul_nonneg (Real.sqrt_nonneg h) (Real.sqrt_nonneg (k+1:ℝ))]
        apply mul_le_mul hinv _ (Real.exp_pos _).le (Real.sqrt_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ ∑ k ∈ Finset.range M, Real.sqrt h * Real.exp (-h*(k:ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intros; positivity
      _ = Real.sqrt h * ∑ k ∈ Finset.range M, Real.exp (-h*(k:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_exp_decay hh h1 M) (Real.sqrt_nonneg h)
  have hsum : (∑ k ∈ low, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) +
      (∑ k ∈ high, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) =
      ∑ k ∈ Finset.range M, (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hcancel : Real.sqrt h*(2/h)=2/Real.sqrt h := by
    have hsq := Real.sq_sqrt hh.le
    field_simp
    nlinarith
  rw [← hsum]
  rw [hcancel] at hhi
  have heq : 2*(2/Real.sqrt h)+2/Real.sqrt h=6/Real.sqrt h := by ring
  linarith


/-- Exponential tilting removes the coarse-gap simplex constraint without a dimension loss. -/
theorem coarse_simplex_sum (r M : ℕ) {h u : ℝ} (hh : 0<h) (h1 : h≤1) :
    (∑ v : Fin r → Fin M, if (∑ i, ((v i).val+1:ℝ)) ≤ u then
      ∏ i, (Real.sqrt ((v i).val+1:ℝ))⁻¹ else 0) ≤
      Real.exp (h*u) * (6/Real.sqrt h)^r := by
  have hev (v : Fin r → Fin M) :
      ∏ i, Real.exp (-h*((v i).val+1:ℝ)) =
        Real.exp (-h*∑ i, ((v i).val+1:ℝ)) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  have hbound :
      (∑ v : Fin r → Fin M, if (∑ i, ((v i).val+1:ℝ)) ≤ u then
        ∏ i, (Real.sqrt ((v i).val+1:ℝ))⁻¹ else 0) ≤
      Real.exp (h*u) * ∑ v : Fin r → Fin M,
        ∏ i, ((Real.sqrt ((v i).val+1:ℝ))⁻¹ * Real.exp (-h*((v i).val+1:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [Finset.prod_mul_distrib, hev]
    split_ifs with hv
    · have he : 1 ≤ Real.exp (h*u) * Real.exp (-h*∑ i, ((v i).val+1:ℝ)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      have hp : 0 ≤ ∏ i, (Real.sqrt ((v i).val+1:ℝ))⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left he hp]
    · positivity
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← Fintype.prod_sum (fun (_i : Fin r) (k : Fin M) =>
    (Real.sqrt (k.val+1:ℝ))⁻¹ * Real.exp (-h*(k.val+1:ℝ)))]
  have hc : (6/Real.sqrt h)^r = ∏ _i : Fin r, (6/Real.sqrt h) := by simp [div_pow]
  rw [hc]
  apply Finset.prod_le_prod₀
  · intros; positivity
  · intro i _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) M]
    exact coarse_laplace_sum hh h1 M

end TraceReconstruction


namespace TraceReconstruction

/-- The degree-series estimate in the common-mass argument, with no asymptotic notation. -/
theorem degree_series_bound (a : ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r)^2 ≤
      2 * Real.exp (2*a^2) := by
  let u (r : ℕ) : ℝ := (Real.sqrt ((1/2:ℝ)^r))
  let v (r : ℕ) : ℝ := (Real.sqrt ((2:ℝ)^r))*a^r/(Real.sqrt (r:ℝ))^r
  have huv (r : ℕ) : u r * v r = a^r/(Real.sqrt (r:ℝ))^r := by
    unfold u v
    have he : Real.sqrt ((1/2:ℝ)^r) * Real.sqrt ((2:ℝ)^r)=1 := by
      rw [← Real.sqrt_mul (by positivity), ← mul_pow]
      norm_num
    calc
      _ = (Real.sqrt ((1/2:ℝ)^r) * Real.sqrt ((2:ℝ)^r)) * (a^r/(Real.sqrt (r:ℝ))^r) := by ring
      _ = _ := by rw [he, one_mul]
  have hu : (∑ r ∈ Finset.range N, (u r)^2) ≤ 2 := by
    simp only [u, Real.sq_sqrt (by positivity : 0 ≤ (1/2:ℝ)^_)]
    have hg := geom_sum_mul_neg (1/2:ℝ) N
    have hp : 0≤(1/2:ℝ)^N := by positivity
    linarith
  have hv : (∑ r ∈ Finset.range N, (v r)^2) ≤ Real.exp (2*a^2) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by positivity) N)
    apply Finset.sum_le_sum
    intro r _
    have hr : 0 < ((r.factorial):ℝ) := by exact_mod_cast Nat.factorial_pos r
    have hrpow : 0 < (r:ℝ)^r := by
      cases r with
      | zero => norm_num
      | succ r => positivity
    have hfac : (r.factorial:ℝ) ≤ (r:ℝ)^r := by exact_mod_cast Nat.factorial_le_pow r
    have hveq : (v r)^2 = (2*a^2)^r / (r:ℝ)^r := by
      unfold v
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hd : ((Real.sqrt (r:ℝ))^r)^2=(r:ℝ)^r := by
        rw [← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt (by positivity)]
      rw [hd]
      rw [← pow_mul, mul_comm r 2, pow_mul]
      ring
    rw [hveq]
    exact div_le_div_of_nonneg_left (by positivity) hr hfac
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) u v
  simp only [huv] at hCS
  exact hCS.trans (mul_le_mul hu hv (by positivity) (by norm_num))

end TraceReconstruction

end
end

end OAI
