import Mathlib

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix

namespace SmoothObstruction.FiniteShears

/-- The finite forward Green solution; no division by a spectral gap. -/
noncomputable def forward (q : ℝ) (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ range t, q ^ (t - 1 - j) * f j

@[simp] lemma forward_zero (q : ℝ) (f : ℕ → ℝ) : forward q f 0 = 0 := by
  simp [forward]

lemma forward_succ (q : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    forward q f (t + 1) = q * forward q f t + f t := by
  simp only [forward, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjt : j < t := mem_range.mp hj
  rw [show t - j = (t - 1 - j) + 1 by omega, pow_succ]
  ring

lemma forward_bound {q M : ℝ} (hq : 0 ≤ q) (hq₁ : q ≤ 1)
    (f : ℕ → ℝ) (t : ℕ) (hf : ∀ j < t, |f j| ≤ M) :
    |forward q f t| ≤ t * M := by
  calc
    _ ≤ ∑ j ∈ range t, |q ^ (t - 1 - j) * f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range t, M := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq _)]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq hq₁) (abs_nonneg _)).trans
        (by simpa using hf j (mem_range.mp hj))
    _ = _ := by simp

/-- A terminal-value Green solution with coefficients at most one when q≥1. -/
noncomputable def backward (N : ℕ) (q : ℝ) (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  -q⁻¹ * forward q⁻¹ (fun j => f (N - 1 - j)) (N - t)

@[simp] lemma backward_terminal (N : ℕ) (q : ℝ) (f : ℕ → ℝ) :
    backward N q f N = 0 := by simp [backward]

lemma backward_succ (N : ℕ) {q : ℝ} (hq : q ≠ 0) (f : ℕ → ℝ)
    (t : ℕ) (ht : t < N) :
    backward N q f (t + 1) = q * backward N q f t + f t := by
  have hn : N - t = (N - (t + 1)) + 1 := by omega
  have ht' : N - 1 - (N - (t + 1)) = t := by omega
  unfold backward
  rw [hn, forward_succ, ht']
  field_simp
  ring

lemma backward_bound (N : ℕ) {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (f : ℕ → ℝ) (t : ℕ) (hf : ∀ j < N, |f j| ≤ M) :
    |backward N q f t| ≤ N * M := by
  have hq₀ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqi : 0 ≤ q⁻¹ := inv_nonneg.mpr hq₀.le
  have hqi₁ : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  by_cases ht : t ≤ N
  · have hbound := forward_bound hqi hqi₁ (fun j => f (N - 1 - j)) (N - t)
      (fun j hj => hf _ (by omega))
    calc
      _ = q⁻¹ * |forward q⁻¹ (fun j => f (N - 1 - j)) (N - t)| := by
        rw [backward, abs_mul, abs_neg, abs_of_nonneg hqi]
      _ ≤ (1 : ℝ) * ((N - t : ℕ) * M) := mul_le_mul hqi₁ hbound (abs_nonneg _) (by positivity)
      _ ≤ N * M := by
        simp only [one_mul]
        apply mul_le_mul_of_nonneg_right _ hM
        exact_mod_cast Nat.sub_le N t
  · simp only [backward, Nat.sub_eq_zero_of_le (by omega : N ≤ t), forward_zero, mul_zero, abs_zero]
    positivity

/-- The scalar input needed by every elementary shear in the finite
triangular cocycle reduction. This includes q=1; it never divides by q−1. -/
theorem exists_bounded_recurrence (N : ℕ) {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (f : ℕ → ℝ) (hf : ∀ t < N, |f t| ≤ M) :
    ∃ u : ℕ → ℝ, (∀ t < N, u (t + 1) = q * u t + f t) ∧
      (∀ t ≤ N, |u t| ≤ N * M) := by
  by_cases hq₁ : q ≤ 1
  · refine ⟨forward q f, fun t _ => forward_succ q f t, ?_⟩
    intro t ht
    exact (forward_bound hq.le hq₁ f t (fun j hj => hf j (hj.trans_le ht))).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hM)
  · exact ⟨backward N q f, fun t ht => backward_succ N hq.ne' f t ht,
      fun t _ => backward_bound N (le_of_lt (lt_of_not_ge hq₁)) hM f t hf⟩

end SmoothObstruction.FiniteShears

namespace SmoothObstruction.TriangularGauge
open SmoothObstruction.FiniteShears

variable {d : ℕ}

/-- Replace one row, retaining the other rows. -/
def rowReplace (U : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (v : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun k j => if k = i then v j else U k j

lemma mul_rowReplace_same {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsUpperTriangular)
    (U : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (v : Fin d → ℝ) :
    (A * rowReplace U i v) i j =
      A i i * v j + ∑ k, if i < k then A i k * U k j else 0 := by
  rw [Matrix.mul_apply]
  have hterm (k : Fin d) : A i k * rowReplace U i v k j =
      (if k = i then A i i * v j else 0) + (if i < k then A i k * U k j else 0) := by
    rcases lt_trichotomy k i with hki | rfl | hik
    · simp [rowReplace, ne_of_lt hki, not_lt_of_ge hki.le, hA hki]
    · simp [rowReplace]
    · simp [rowReplace, ne_of_gt hik, hik]
  simp_rw [hterm]
  rw [sum_add_distrib]
  simp

lemma mul_rowReplace_later {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsUpperTriangular)
    (U : Matrix (Fin d) (Fin d) ℝ) (i k j : Fin d) (v : Fin d → ℝ) (hik : i < k) :
    (A * rowReplace U i v) k j = (A * U) k j := by
  simp only [Matrix.mul_apply]
  apply sum_congr rfl
  intro l _
  by_cases hli : l = i
  · subst l
    simp [hA hik]
  · simp [rowReplace, hli]

lemma forcing_zero {U : Matrix (Fin d) (Fin d) ℝ} (hU : U.IsUpperTriangular)
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (hji : j ≤ i) :
    (∑ k, if i < k then A i k * U k j else 0) = 0 := by
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · simp [hik, hU (hji.trans_lt hik)]
  · simp [hik]

lemma forcing_bound (A U : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d)
    {H M : ℝ} (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hA : ∀ k l, |A k l| ≤ H) (hU : ∀ k l, |U k l| ≤ M) :
    |∑ k, if i < k then A i k * U k j else 0| ≤ d * H * M := by
  calc
    _ ≤ ∑ k, |if i < k then A i k * U k j else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, H * M := by
      apply sum_le_sum
      intro k _
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (hA i k) (hU k j) (abs_nonneg _) hH
      · simp only [abs_zero]
        positivity
    _ = _ := by simp; ring


/-- A full finite-time unitriangular diagonalizing gauge. In contrast to
infinite-time reducibility, this assertion needs no separation of rates.
All losses are fixed-degree polynomials in the length and entry bound. -/
theorem exists_diagonal_gauge (N : ℕ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d → ℝ) {H : ℝ} (hH : 1 ≤ H)
    (ha : ∀ j, 0 < a j) (hai : ∀ j, |(a j)⁻¹| ≤ H)
    (htri : ∀ t < N, (A t).IsUpperTriangular)
    (hdiag : ∀ t < N, ∀ j, A t j j = a j)
    (hbound : ∀ t < N, ∀ i j, |A t i j| ≤ H) :
    ∃ U : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t, (U t).IsUpperTriangular ∧ ∀ j, U t j j = 1) ∧
      (∀ t ≤ N, ∀ i j, |U t i j| ≤ (1 + N * d * H ^ 2) ^ d) ∧
      (∀ t < N, A t * U t = U (t + 1) * Matrix.diagonal a) := by
  classical
  let K : ℝ := 1 + N * d * H ^ 2
  have hK : 1 ≤ K := by
    dsimp [K]
    exact le_add_of_nonneg_right (by positivity)
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hind (r : ℕ) (hr : r ≤ d) :
      ∃ U : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, (U t).IsUpperTriangular ∧ ∀ j, U t j j = 1) ∧
        (∀ t ≤ N, ∀ i j, |U t i j| ≤ K ^ r) ∧
        (∀ t < N, ∀ i, d - r ≤ i.val → ∀ j,
          (A t * U t) i j = a j * U (t + 1) i j) := by
    induction r with
    | zero =>
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · intro t
        refine ⟨?_, fun j => by simp⟩
        intro i j hji
        change j < i at hji
        simp [ne_of_gt hji]
      · intro t ht i j
        simp only [Matrix.one_apply, pow_zero]
        split_ifs <;> norm_num
      · intro t ht i hi
        simp only [Nat.sub_zero] at hi
        exact (not_le_of_gt i.isLt hi).elim
    | succ r ih =>
      obtain ⟨U, hUtri, hUb, hUeq⟩ := ih (by omega)
      let i : Fin d := ⟨d - (r + 1), by omega⟩
      let M : ℝ := K ^ r
      have hM : 0 ≤ M := pow_nonneg hK₀ r
      let R (j : Fin d) (t : ℕ) : ℝ :=
        ∑ k, if i < k then A t i k * U t k j else 0
      let f (j : Fin d) (t : ℕ) : ℝ := (a j)⁻¹ * R j t
      have hf (j : Fin d) (t : ℕ) (ht : t < N) :
          |f j t| ≤ H * (d * H * M) := by
        change |(a j)⁻¹ * R j t| ≤ _
        rw [abs_mul]
        exact mul_le_mul (hai j)
          (forcing_bound (A t) (U t) i j hH₀ hM (hbound t ht) (hUb t ht.le))
          (abs_nonneg _) hH₀
      have hforce : 0 ≤ H * (d * H * M) := by positivity
      have hrex (j : Fin d) := exists_bounded_recurrence N
        (div_pos (ha i) (ha j)) hforce (f j) (hf j)
      choose u hurec hub using hrex
      let v (t : ℕ) (j : Fin d) : ℝ :=
        if i < j then u j t else if j = i then 1 else 0
      let V (t : ℕ) := rowReplace (U t) i (v t)
      have hKM : K * M = K ^ (r + 1) := by dsimp [M]; rw [pow_succ]; ring
      have hMB : M ≤ K ^ (r + 1) := by
        rw [← hKM]
        exact le_mul_of_one_le_left hM hK
      have hNB : (N : ℝ) * (H * (d * H * M)) ≤ K ^ (r + 1) := by
        rw [← hKM]
        dsimp [K]
        nlinarith
      have hv (t : ℕ) (ht : t ≤ N) (j : Fin d) : |v t j| ≤ K ^ (r + 1) := by
        dsimp [v]
        split_ifs with hij hji
        · exact (hub j t ht).trans hNB
        · simpa using one_le_pow₀ hK
        · simpa using pow_nonneg hK₀ (r + 1)
      refine ⟨V, ?_, ?_, ?_⟩
      · intro t
        constructor
        · intro k j hjk
          change j < k at hjk
          dsimp [V, rowReplace]
          split_ifs with hki
          · subst k
            simp [v, not_lt_of_ge hjk.le, ne_of_lt hjk]
          · exact (hUtri t).1 hjk
        · intro j
          dsimp [V, rowReplace]
          split_ifs with hji
          · subst j
            simp [v]
          · exact (hUtri t).2 j
      · intro t ht k j
        dsimp [V, rowReplace]
        split_ifs
        · exact hv t ht j
        · exact (hUb t ht k j).trans hMB
      · intro t ht k hk j
        by_cases hki : k = i
        · subst k
          rw [show V t = rowReplace (U t) i (v t) from rfl,
            mul_rowReplace_same (htri t ht), hdiag t ht]
          rw [show V (t + 1) i j = v (t + 1) j by simp [V, rowReplace]]
          change a i * v t j + R j t = a j * v (t + 1) j
          by_cases hij : i < j
          · simp only [v, ite_eq_left hij]
            rw [hurec j t ht]
            dsimp [f]
            field_simp [(ha j).ne']
          · have hR : R j t = 0 := forcing_zero (hUtri t).1 (A t) i j (le_of_not_gt hij)
            rw [hR]
            by_cases hji : j = i
            · subst j
              simp [v]
            · simp [v, hij, hji]
        · have hik : i < k := lt_of_le_of_ne hk (Ne.symm hki)
          have hk' : d - r ≤ k.val := by
            have hval : i.val < k.val := hik
            dsimp [i] at hval
            omega
          rw [show V t = rowReplace (U t) i (v t) from rfl,
            mul_rowReplace_later (htri t ht) (U t) i k j (v t) hik,
            hUeq t ht k hk']
          simp [V, rowReplace, hki]
  obtain ⟨U, hUt, hUb, hUeq⟩ := hind d le_rfl
  refine ⟨U, hUt, hUb, ?_⟩
  intro t ht
  ext i j
  rw [Matrix.mul_diagonal]
  exact (hUeq t ht i (by omega) j).trans (mul_comm _ _)

/-- A deliberately coarse finite-dimensional determinant estimate. -/
lemma abs_det_le_entry_bound (A : Matrix (Fin d) (Fin d) ℝ) {B : ℝ}
    (hA : ∀ i j, |A i j| ≤ B) :
    |A.det| ≤ (Nat.factorial d : ℝ) * B ^ d := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin d), ∏ i, |A (σ i) i| := by
      apply sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), B ^ d := by
      apply sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _i : Fin d, B := prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

lemma unitriangular_det {U : Matrix (Fin d) (Fin d) ℝ}
    (ht : U.IsUpperTriangular) (hd : ∀ i, U i i = 1) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [hd]

lemma unitriangular_inverse_bound {U : Matrix (Fin d) (Fin d) ℝ} {B : ℝ}
    (ht : U.IsUpperTriangular) (hd : ∀ i, U i i = 1) (hB : 1 ≤ B)
    (hb : ∀ i j, |U i j| ≤ B) (i j : Fin d) :
    |U⁻¹ i j| ≤ (Nat.factorial d : ℝ) * B ^ d := by
  have hdet := unitriangular_det ht hd
  rw [Matrix.inv_def, hdet]
  simp only [Ring.inverse_one, one_smul, Matrix.adjugate_apply]
  apply abs_det_le_entry_bound _
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split_ifs
    · simpa using hB
    · simpa using (zero_le_one.trans hB)
  · simpa [Matrix.updateRow_ne hk] using hb k l

/-- The gauge can be chosen with a polynomially bounded genuine inverse. -/
theorem exists_diagonal_gauge_invertible (N : ℕ)
    (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ)
    {H : ℝ} (hH : 1 ≤ H) (ha : ∀ j, 0 < a j)
    (hai : ∀ j, |(a j)⁻¹| ≤ H)
    (htri : ∀ t < N, (A t).IsUpperTriangular)
    (hdiag : ∀ t < N, ∀ j, A t j j = a j)
    (hbound : ∀ t < N, ∀ i j, |A t i j| ≤ H) :
    ∃ U : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t, U t * (U t)⁻¹ = 1 ∧ (U t)⁻¹ * U t = 1) ∧
      (∀ t ≤ N, ∀ i j, |U t i j| ≤ (1 + N * d * H ^ 2) ^ d) ∧
      (∀ t ≤ N, ∀ i j, |(U t)⁻¹ i j| ≤
        (Nat.factorial d : ℝ) * ((1 + N * d * H ^ 2) ^ d) ^ d) ∧
      (∀ t < N, (U (t + 1))⁻¹ * A t * U t = Matrix.diagonal a) := by
  obtain ⟨U, hUt, hUb, hUeq⟩ := exists_diagonal_gauge N A a hH ha hai htri hdiag hbound
  have hu (t : ℕ) : IsUnit (U t).det := by
    rw [unitriangular_det (hUt t).1 (hUt t).2]
    exact isUnit_one
  refine ⟨U, fun t => ⟨Matrix.mul_nonsing_inv _ (hu t), Matrix.nonsing_inv_mul _ (hu t)⟩,
    hUb, ?_, ?_⟩
  · intro t ht i j
    exact unitriangular_inverse_bound (hUt t).1 (hUt t).2
      (one_le_pow₀ (le_add_of_nonneg_right (by positivity))) (hUb t ht) i j
  · intro t ht
    rw [Matrix.mul_assoc, hUeq t ht, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (hu (t + 1)), Matrix.one_mul]

end SmoothObstruction.TriangularGauge

namespace SmoothObstruction.NormalizedGauge
open SmoothObstruction.TriangularGauge
variable {d : ℕ}

noncomputable def error (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) : ℝ :=
  ∑ a ∈ range t, (Real.log (A a j j) - lam j)

lemma error_succ (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) :
    error A lam (t + 1) j = error A lam t j + Real.log (A t j j) - lam j := by
  simp only [error, sum_range_succ]
  ring

noncomputable def normalized (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => Real.exp (-error A lam (t + 1) i) * A t i j * Real.exp (error A lam t j)

lemma normalized_tri (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (ht : (A t).IsUpperTriangular) :
    (normalized A lam t).IsUpperTriangular := by
  intro i j hji
  simp [normalized, ht hji]

lemma normalized_diag (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) (hpos : 0 < A t j j) :
    normalized A lam t j j = Real.exp (lam j) := by
  unfold normalized
  rw [← Real.exp_log hpos, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [error_succ]
  ring

lemma normalized_bound (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) {R E : ℝ}
    (hA : ∀ i j, |A t i j| ≤ Real.exp R)
    (hprev : ∀ j, |error A lam t j| ≤ E)
    (hnext : ∀ j, |error A lam (t + 1) j| ≤ E) (i j : Fin d) :
    |normalized A lam t i j| ≤ Real.exp (R + 2 * E) := by
  have hi : -error A lam (t + 1) i ≤ E := by
    have := (abs_le.mp (hnext i)).1
    linarith
  have hj : error A lam t j ≤ E := le_trans (le_abs_self _) (hprev j)
  calc
    _ = Real.exp (-error A lam (t + 1) i) * |A t i j| * Real.exp (error A lam t j) := by
      simp [normalized, abs_mul]
    _ ≤ Real.exp E * Real.exp R * Real.exp E := by
      gcongr
      exact hA i j
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Diagonal chord normalization followed by a finite bounded shear gauge. -/
theorem exists_normalized_gauge (N : ℕ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) {R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    (htri : ∀ t < N, (A t).IsUpperTriangular)
    (hpos : ∀ t < N, ∀ j, 0 < A t j j)
    (hA : ∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R)
    (hlam : ∀ j, |lam j| ≤ R)
    (he : ∀ t ≤ N, ∀ j, |error A lam t j| ≤ E) :
    ∃ C V : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t, C t * V t = 1 ∧ V t * C t = 1) ∧
      (∀ t ≤ N, ∀ i j, |C t i j| ≤ Real.exp E *
        (1 + N * d * (Real.exp (R + 2 * E)) ^ 2) ^ d) ∧
      (∀ t ≤ N, ∀ i j, |V t i j| ≤ (Nat.factorial d : ℝ) *
        ((1 + N * d * (Real.exp (R + 2 * E)) ^ 2) ^ d) ^ d * Real.exp E) ∧
      (∀ t < N, A t * C t = C (t + 1) * Matrix.diagonal (fun j => Real.exp (lam j))) := by
  let H := Real.exp (R + 2 * E)
  let a := fun j => Real.exp (lam j)
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr (by positivity)
  have hai (j : Fin d) : |(a j)⁻¹| ≤ H := by
    dsimp [a, H]
    rw [← Real.exp_neg, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hlam j)).1
    linarith
  obtain ⟨U, hUt, hUb, hUeq⟩ := exists_diagonal_gauge N (normalized A lam) a hH
    (fun j => Real.exp_pos _) hai
    (fun t ht => normalized_tri A lam t (htri t ht))
    (fun t ht j => normalized_diag A lam t j (hpos t ht j))
    (fun t ht i j => normalized_bound A lam t (hA t ht)
      (he t ht.le) (he (t + 1) (by omega)) i j)
  let D (t : ℕ) := Matrix.diagonal (fun j => Real.exp (error A lam t j))
  let E' (t : ℕ) := Matrix.diagonal (fun j => Real.exp (-error A lam t j))
  have hDE (t : ℕ) : D t * E' t = 1 := by
    dsimp only [D, E']
    rw [Matrix.diagonal_mul_diagonal]
    simp [← Real.exp_add]
  have hED (t : ℕ) : E' t * D t = 1 := by
    dsimp only [D, E']
    rw [Matrix.diagonal_mul_diagonal]
    simp [← Real.exp_add]
  have hdet (t : ℕ) : IsUnit (U t).det := by
    rw [unitriangular_det (hUt t).1 (hUt t).2]
    exact isUnit_one
  have hnorm (t : ℕ) : A t * D t = D (t + 1) * normalized A lam t := by
    ext i j
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul, normalized]
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  refine ⟨fun t => D t * U t, fun t => (U t)⁻¹ * E' t, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · calc
        _ = D t * (U t * (U t)⁻¹) * E' t := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ (hdet t), Matrix.mul_one, hDE]
    · calc
        _ = (U t)⁻¹ * (E' t * D t) * U t := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hED, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet t)]
  · intro t ht i j
    dsimp only [D]
    rw [Matrix.diagonal_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hUb t ht i j) (abs_nonneg _) (Real.exp_nonneg _)
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (he t ht i))
  · intro t ht i j
    dsimp only [E']
    rw [Matrix.mul_diagonal, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul
      (unitriangular_inverse_bound (hUt t).1 (hUt t).2
        (one_le_pow₀ (le_add_of_nonneg_right (by positivity))) (hUb t ht) i j)
      _ (Real.exp_nonneg _) (by positivity)
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (he t ht j)).1
    linarith
  · intro t ht
    rw [← Matrix.mul_assoc, hnorm, Matrix.mul_assoc, hUeq t ht, ← Matrix.mul_assoc]

lemma gauge_polynomial_le_exp (d N : ℕ) {R E : ℝ} (hR : 0 ≤ R)
    (hE : 1 ≤ E) (hN : (N : ℝ) ≤ Real.exp E) :
    1 + N * d * (Real.exp (R + 2 * E)) ^ 2 ≤
      Real.exp ((2 * R + d + 6) * E) := by
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hd : (d : ℝ) ≤ Real.exp ((d : ℝ) * E) := by
    calc
      (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) hE)
  have hH : (Real.exp (R + 2 * E)) ^ 2 ≤ Real.exp ((2 * R + 4) * E) := by
    rw [sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hT : (0 : ℝ) ≤ (2 * R + d + 5) * E := by positivity
  have hsum : 1 + Real.exp ((2 * R + d + 5) * E) ≤
      Real.exp E * Real.exp ((2 * R + d + 5) * E) := by
    have hone := Real.one_le_exp_iff.mpr hT
    have htwo : (2 : ℝ) ≤ Real.exp E := calc
      2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr hE
    nlinarith
  calc
    _ ≤ 1 + Real.exp E * Real.exp ((d : ℝ) * E) * Real.exp ((2 * R + 4) * E) := by
      gcongr
    _ = 1 + Real.exp ((2 * R + d + 5) * E) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hsum
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform exponential estimates with a constant depending only on d and R.
This is the finite gauge estimate `eq:finite-gauge` before conversion of the
entry norm to the Euclidean operator norm. -/
theorem exists_exponential_gauge (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (E : ℝ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ), 1 ≤ E → Real.log (N + 1) ≤ E →
      (∀ t < N, (A t).IsUpperTriangular) →
      (∀ t < N, ∀ j, 0 < A t j j) →
      (∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R) →
      (∀ j, |lam j| ≤ R) →
      (∀ t ≤ N, ∀ j, |error A lam t j| ≤ E) →
      ∃ U V : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, U t * V t = 1 ∧ V t * U t = 1) ∧
        (∀ t ≤ N, ∀ i j, |U t i j| ≤ Real.exp (C * E)) ∧
        (∀ t ≤ N, ∀ i j, |V t i j| ≤ Real.exp (C * E)) ∧
        (∀ t < N, A t * U t = U (t + 1) * Matrix.diagonal (fun j => Real.exp (lam j))) := by
  let c : ℝ := 2 * R + d + 6
  let C : ℝ := 1 + Nat.factorial d + (d + d * d) * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N E A lam hE hlog htri hpos hA hlam he
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hN : (N : ℝ) ≤ Real.exp E := by
    calc
      (N : ℝ) ≤ N + 1 := by linarith
      _ = Real.exp (Real.log (N + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  obtain ⟨U, V, hUV, hUb, hVb, hEq⟩ := exists_normalized_gauge N A lam hR hE₀
    htri hpos hA hlam he
  have hK := gauge_polynomial_le_exp d N hR hE hN
  have hb : 0 ≤ 1 + (N : ℝ) * d * (Real.exp (R + 2 * E)) ^ 2 := by positivity
  have hpow : (1 + (N : ℝ) * d * (Real.exp (R + 2 * E)) ^ 2) ^ d ≤
      Real.exp ((d : ℝ) * c * E) := by
    calc
      _ ≤ (Real.exp (c * E)) ^ d := pow_le_pow_left₀ hb hK d
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfac : (Nat.factorial d : ℝ) ≤ Real.exp ((Nat.factorial d : ℝ) * E) := by
    calc
      _ ≤ Real.exp (Nat.factorial d : ℝ) := by linarith [Real.add_one_le_exp (Nat.factorial d : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) hE)
  refine ⟨U, V, hUV, ?_, ?_, hEq⟩
  · intro t ht i j
    calc
      _ ≤ _ := hUb t ht i j
      _ ≤ Real.exp E * Real.exp ((d : ℝ) * c * E) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
      _ = Real.exp ((1 + d * c) * E) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) * d by positivity) hc,
          show 0 ≤ (Nat.factorial d : ℝ) by positivity]
  · intro t ht i j
    calc
      _ ≤ _ := hVb t ht i j
      _ ≤ Real.exp ((Nat.factorial d : ℝ) * E) *
          (Real.exp ((d : ℝ) * c * E)) ^ d * Real.exp E := by
        gcongr
      _ = Real.exp (((Nat.factorial d : ℝ) + d * d * c + 1) * E) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity) hc]

end SmoothObstruction.NormalizedGauge

end

end OAI
