import OAI.Probability.FreeIsing.Estimates.ExponentialTaylor

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology NNReal

namespace Problem367.ExponentialTaylor

theorem norm_gaussian_recurrence_error_le_sum
    (z : ℕ → ℂ) (dt e : ℕ → ℝ) (n : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (hdt : ∀ k < n, 0 ≤ dt k)
    (he : ∀ k < n,
      ‖z (k + 1) - Complex.exp ((-c * dt k : ℝ) : ℂ) * z k‖ ≤ e k) :
    ‖z n - Complex.exp (((-c * ∑ k ∈ Finset.range n, dt k : ℝ) : ℂ)) * z 0‖ ≤
      ∑ k ∈ Finset.range n, e k := by
  have h := norm_recurrence_error_le_sum z
    (fun k => Complex.exp ((-c * dt k : ℝ) : ℂ)) e n
    (fun k hk => ?_) he
  · simpa only [← Complex.exp_sum, ← Complex.ofReal_sum, ← Finset.mul_sum] using h
  · rw [Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (hdt k hk))

theorem eq_gaussian_mul_of_recurrence_errors_tendsto_zero
    {ι : Type*} {l : Filter ι} [NeBot l]
    (z : ι → ℕ → ℂ) (dt e : ι → ℕ → ℝ) (N : ι → ℕ)
    {c T : ℝ} {z₀ zT : ℂ}
    (hc : 0 ≤ c)
    (hdt : ∀ i k, k < N i → 0 ≤ dt i k)
    (htotal : ∀ i, ∑ k ∈ Finset.range (N i), dt i k = T)
    (hstart : ∀ i, z i 0 = z₀) (hend : ∀ i, z i (N i) = zT)
    (he : ∀ i k, k < N i →
      ‖z i (k + 1) - Complex.exp ((-c * dt i k : ℝ) : ℂ) * z i k‖ ≤ e i k)
    (hlim : Tendsto (fun i => ∑ k ∈ Finset.range (N i), e i k) l (𝓝 0)) :
    zT = Complex.exp ((-c * T : ℝ) : ℂ) * z₀ := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun i => by
    simpa only [htotal i, hstart i, hend i] using
      norm_gaussian_recurrence_error_le_sum (z i) (dt i) (e i) (N i) hc (hdt i) (he i)

theorem sum_mul_sqrt_le_total_mul_sqrt_mesh
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, dt k * Real.sqrt (dt k)) ≤
      (∑ k ∈ Finset.range n, dt k) * Real.sqrt mesh := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmesh k (Finset.mem_range.mp hk)))
    (hdt k (Finset.mem_range.mp hk))

theorem sum_sq_le_total_mul_mesh
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, (dt k) ^ 2) ≤
      (∑ k ∈ Finset.range n, dt k) * mesh := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  simpa only [pow_two] using mul_le_mul_of_nonneg_left
    (hmesh k (Finset.mem_range.mp hk)) (hdt k (Finset.mem_range.mp hk))

theorem sum_cube_le_total_mul_mesh_sq
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, (dt k) ^ 3) ≤
      (∑ k ∈ Finset.range n, dt k) * mesh ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hsq : (dt k) ^ 2 ≤ mesh ^ 2 :=
    pow_le_pow_left₀ (hdt k hk') (hmesh k hk') 2
  convert mul_le_mul_of_nonneg_left hsq (hdt k hk') using 1; ring

theorem tendsto_sum_brownian_drift_errors
    {ι : Type*} {l : Filter ι}
    (dt : ι → ℕ → ℝ) (N : ι → ℕ) (mesh : ι → ℝ)
    {T A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hdt : ∀ i k, k < N i → 0 ≤ dt i k)
    (hmesh : ∀ i k, k < N i → dt i k ≤ mesh i)
    (htotal : ∀ i, ∑ k ∈ Finset.range (N i), dt i k = T)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun i => ∑ k ∈ Finset.range (N i),
      (A * (dt i k * Real.sqrt (dt i k)) + B * (dt i k) ^ 2 + C * (dt i k) ^ 3))
      l (𝓝 0) := by
  have hupper (i) : (∑ k ∈ Finset.range (N i),
      (A * (dt i k * Real.sqrt (dt i k)) + B * (dt i k) ^ 2 + C * (dt i k) ^ 3)) ≤
      A * (T * Real.sqrt (mesh i)) + B * (T * mesh i) + C * (T * (mesh i) ^ 2) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [htotal i] using (sum_mul_sqrt_le_total_mul_sqrt_mesh
            (dt i) (N i) (hdt i) (hmesh i))) hA
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [htotal i] using (sum_sq_le_total_mul_mesh
            (dt i) (N i) (hdt i) (hmesh i))) hB
    · exact mul_le_mul_of_nonneg_left
        (by simpa only [htotal i] using (sum_cube_le_total_mul_mesh_sq
          (dt i) (N i) (hdt i) (hmesh i))) hC
  have hright : Tendsto (fun i => A * (T * Real.sqrt (mesh i)) +
      B * (T * mesh i) + C * (T * (mesh i) ^ 2)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul T |>.const_mul A).add
        ((hlim.const_mul T).const_mul B) |>.add (((hlim.pow 2).const_mul T).const_mul C)
  apply squeeze_zero (fun i => ?_) hupper hright
  apply Finset.sum_nonneg
  intro k hk
  have := hdt i k (Finset.mem_range.mp hk)
  positivity

theorem eq_gaussian_mul_of_local_error
    (z : ℝ → ℂ) {c T A B C : ℝ}
    (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hstep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ‖z t - Complex.exp ((-c * (t - s) : ℝ) : ℂ) * z s‖ ≤
        A * ((t - s) * Real.sqrt (t - s)) + B * (t - s) ^ 2 + C * (t - s) ^ 3) :
    z T = Complex.exp ((-c * T : ℝ) : ℂ) * z 0 := by
  let mesh : ℕ → ℝ := fun n => T / ((n : ℝ) + 1)
  let grid : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * mesh n
  let e : ℕ → ℕ → ℝ := fun n _ =>
    A * (mesh n * Real.sqrt (mesh n)) + B * (mesh n) ^ 2 + C * (mesh n) ^ 3
  have hm (n : ℕ) : 0 ≤ mesh n := by dsimp [mesh]; positivity
  have htotal (n : ℕ) : (∑ _k ∈ Finset.range (n + 1), mesh n) = T := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    dsimp [mesh]
    field_simp
  have hmeshlim : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  have herrlim : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), e n k) atTop (𝓝 0) :=
    tendsto_sum_brownian_drift_errors (fun n _ => mesh n) (fun n => n + 1) mesh
      hA hB hC (fun n _ _ => hm n) (fun _ _ _ => le_rfl) htotal hmeshlim
  apply eq_gaussian_mul_of_recurrence_errors_tendsto_zero
    (fun n k => z (grid n k)) (fun n _ => mesh n) e (fun n => n + 1) hc
    (fun n _ _ => hm n) htotal (fun n => by simp [grid])
    (fun n => ?_) (fun n k hk => ?_) herrlim
  · congr 1
    dsimp [grid, mesh]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  · have hkn : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_of_lt hk)
    have hstart : 0 ≤ grid n k := mul_nonneg (Nat.cast_nonneg k) (hm n)
    have hdiff : grid n (k + 1) - grid n k = mesh n := by
      simp only [grid, Nat.cast_add, Nat.cast_one]
      ring
    have horder : grid n k ≤ grid n (k + 1) := by linarith [hm n]
    have hend : grid n (k + 1) ≤ T := by
      calc
        grid n (k + 1) = ((k : ℝ) + 1) * mesh n := by simp [grid]
        _ ≤ ((n : ℝ) + 1) * mesh n := mul_le_mul_of_nonneg_right hkn (hm n)
        _ = T := by dsimp [mesh]; field_simp
    simpa only [hdiff, e] using hstep (grid n k) (grid n (k + 1)) hstart horder hend

theorem eq_gaussian_mul_of_local_error_nnreal
    (z : ℝ≥0 → ℂ) (T : ℝ≥0) {c A B C : ℝ}
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hstep : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ‖z t - Complex.exp ((-c * ((t : ℝ) - (s : ℝ)) : ℝ) : ℂ) * z s‖ ≤
        A * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
          B * ((t : ℝ) - (s : ℝ)) ^ 2 + C * ((t : ℝ) - (s : ℝ)) ^ 3) :
    z T = Complex.exp ((-c * (T : ℝ) : ℝ) : ℂ) * z 0 := by
  have h := eq_gaussian_mul_of_local_error (fun r => z r.toNNReal) hc T.coe_nonneg
    hA hB hC (fun s t hs hst ht => ?_)
  · simpa only [Real.toNNReal_coe, Real.toNNReal_zero] using h
  · have ht0 : 0 ≤ t := hs.trans hst
    have hst' : s.toNNReal ≤ t.toNNReal := Real.toNNReal_mono hst
    have ht' : t.toNNReal ≤ T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht
    simpa only [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht0] using
      hstep s.toNNReal t.toNNReal hst' ht'

end Problem367.ExponentialTaylor

end

end OAI
