import OAI.Probability.FreeIsing.Trees.ResponseRowEnergy

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem367.ResponseRows

section Deterministic

variable {Ω ι : Type*}

theorem norm_tree_coefficient_le
    {d : ℕ} {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (s : TreeVertex d → Finset ι) (X : TreeVertex d → ι → Ω → ℝ)
    (v : TreeVertex d) (ω : Ω) :
    ‖coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω‖ ≤
      theta ^ v.1.length := by
  have hp := prod_responseAttenuation_pos (s v) (fun i => X v i ω) hθ
  have hle := prod_attenuation_le_one (s v) (fun i => X v i ω) hθ
  have hw : 0 ≤ theta ^ v.1.length := pow_nonneg hθ0 _
  rw [coefficient, pathProduct, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw,
    abs_of_pos hp]
  exact mul_le_of_le_one_right hw hle

theorem summable_tree_coefficient_sq
    {d : ℕ} {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1)
    (s : TreeVertex d → Finset ι) (X : TreeVertex d → ι → Ω → ℝ) (ω : Ω) :
    Summable (fun v : TreeVertex d =>
      (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    summable_norm_sq_of_radial_bound d hsub
      (fun v => coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω)
      (fun v => norm_tree_coefficient_le hθ0 hθ s X v ω)

theorem summable_regularPathWeight {d : ℕ} {theta : ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (regularPathWeight d theta) := by
  have hs := summable_regularPathWeight_mul_length_sq hsub
  apply Summable.of_nonneg_of_le (regularPathWeight_nonneg d theta) _ hs
  intro n
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hr2 (regularPathWeight_nonneg d theta n)

theorem summable_regularPathWeight_sqrt_length_sq
    {d : ℕ} {theta A : ℝ} (hA : 0 ≤ A)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (fun n => regularPathWeight d theta n *
      Real.sqrt (A * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs := (summable_regularPathWeight_mul_length_sq hsub).mul_left (Real.sqrt A)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg
    (regularPathWeight_nonneg d theta n) (Real.sqrt_nonneg _)) _ hs
  intro n
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [Real.sqrt_mul hA, Real.sqrt_sq (Nat.cast_nonneg _)]
  have hr2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  calc
    regularPathWeight d theta n * (Real.sqrt A * ((n + 1 : ℕ) : ℝ)) ≤
        regularPathWeight d theta n * (Real.sqrt A * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hr2 (Real.sqrt_nonneg A))
        (regularPathWeight_nonneg d theta n)
    _ = _ := by ring

end Deterministic

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_tree_density_le_subcritical
    {d : ℕ} {ι : Type*} (s : TreeVertex d → Finset ι)
    (hcard : ∀ v, (s v).card = v.1.length)
    {theta C : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) (hC : 0 ≤ C)
    {X Y : TreeVertex d → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ v i, i ∈ s v → Measurable (X v i))
    (hY : ∀ v i, i ∈ s v → Measurable (Y v i))
    (hInt : ∀ v i, i ∈ s v → Integrable (fun ω => (X v i ω - Y v i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    (hlog : ∀ v i, i ∈ s v →
      (∫ ω, (Real.log (responseAttenuation theta (X v i ω)) -
        Real.log (responseAttenuation theta (Y v i ω))) ^ 2 ∂μ) ≤
        C * (∫ ω, (H ω - H' ω) ^ 2 ∂μ)) :
    let c := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X
    let c' := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y
    Integrable (DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      subcriticalPathConstant d theta (2 * C) * (∫ ω, (H ω - H' ω) ^ 2 ∂μ) := by
  dsimp only
  let V := ∫ ω, (H ω - H' ω) ^ 2 ∂μ
  let Q := fun n : ℕ => (2 * C) * ((n + 1 : ℕ) : ℝ) ^ 2 * V
  let L := fun _ : ℕ => V
  have hV : 0 ≤ V := integral_nonneg (fun ω => sq_nonneg _)
  have hQ0 (n : ℕ) : 0 ≤ Q n := by dsimp [Q]; positivity
  have hL0 (n : ℕ) : 0 ≤ L n := hV
  have hQ (n : ℕ) (v : TreeVertex d) (hv : v.1.length = n + 1) :
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤ Q n := by
    have h := integral_weighted_path_log_sq_le (s v) hθ (hX v) (hY v) (hInt v) (hlog v)
    rw [hcard v, hv] at h
    change _ ≤ _ at h
    calc
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤
          2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (C * V) := h
      _ = Q n := by dsimp [Q]; ring
  have hL (n : ℕ) (v : TreeVertex d) (_hv : v.1.length = n + 1) :
      pathLinearEnergy μ theta (s v) (X v) (fun ω => H ω - H' ω) ≤ L n :=
    (integral_mul_prod_responseAttenuation_sq_le (s v) hθ (hX v) hU).2
  have hQs : Summable (fun n => regularPathWeight d theta n * Q n) := by
    convert! (summable_regularPathWeight_mul_length_sq hsub).mul_left (2 * C * V) using 1
    funext n
    dsimp only [Q]
    ring
  have hLs : Summable (fun n => regularPathWeight d theta n * L n) :=
    (summable_regularPathWeight hsub).mul_right V
  have hRs : Summable (fun n => regularPathWeight d theta n * Real.sqrt (Q n)) := by
    convert! summable_regularPathWeight_sqrt_length_sq (A := 2 * C * V)
      (by positivity) hsub using 1
    funext n
    congr 2
    dsimp only [Q]
    ring
  have hrows : ∀ᵐ ω ∂μ,
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) ∧
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y v ω) ^ 2) := by
    filter_upwards [] with ω
    exact ⟨summable_tree_coefficient_sq hθ0 hθ hsub s X ω,
      summable_tree_coefficient_sq hθ0 hθ hsub s Y ω⟩
  have hb := integral_tree_density_le_shell_energies s hcard hθ hX hY hInt hH hH' hU
    hQ0 hL0 hQ hL hQs hLs hRs hrows
  refine ⟨hb.1, ?_⟩
  exact (subcritical_noise_drift_bound hsub (by positivity : 0 ≤ 2 * C) hV
    hQ0 hL0 (fun n => le_rfl) (fun n => le_rfl) hb.2).2

theorem eq_zero_of_subcritical_response_variance_identity
    {d : ℕ} {ι : Type*} (s : TreeVertex d → Finset ι)
    (hcard : ∀ v, (s v).card = v.1.length)
    {theta C T : ℝ} (hθ0 : 0 ≤ theta) (hθ : theta ^ 2 ≤ 1)
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) (hC : 0 ≤ C)
    {X Y : ℝ → TreeVertex d → ι → Ω → ℝ} {H H' : ℝ → Ω → ℝ}
    (hX : ∀ t ∈ Icc 0 T, ∀ v i, i ∈ s v → Measurable (X t v i))
    (hY : ∀ t ∈ Icc 0 T, ∀ v i, i ∈ s v → Measurable (Y t v i))
    (hInt : ∀ t ∈ Icc 0 T, ∀ v i, i ∈ s v →
      Integrable (fun ω => (X t v i ω - Y t v i ω) ^ 2) μ)
    (hH : ∀ t ∈ Icc 0 T, Measurable (H t))
    (hH' : ∀ t ∈ Icc 0 T, Measurable (H' t))
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun ω => H t ω - H' t ω) 2 μ)
    (hlog : ∀ t ∈ Icc 0 T, ∀ v i, i ∈ s v →
      (∫ ω, (Real.log (responseAttenuation theta (X t v i ω)) -
        Real.log (responseAttenuation theta (Y t v i ω))) ^ 2 ∂μ) ≤
        C * (∫ ω, (H t ω - H' t ω) ^ 2 ∂μ))
    (hAC : AbsolutelyContinuousOnInterval (fun t => ∫ ω, (H t ω - H' t ω) ^ 2 ∂μ) 0 T)
    (hzero : (∫ ω, (H 0 ω - H' 0 ω) ^ 2 ∂μ) = 0)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv (fun r => ∫ ω, (H r ω - H' r ω) ^ 2 ∂μ) t =
        ∫ ω, DiscrepancyEnergy.density
          (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s (X t))
          (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s (Y t))
          (fun ω => H t ω - H' t ω)
          (fun ω => Real.tanh (H t ω)) (fun ω => Real.tanh (H' t ω)) ω ∂μ) :
    ∀ t ∈ Icc 0 T, (∫ ω, (H t ω - H' t ω) ^ 2 ∂μ) = 0 := by
  apply eq_zero_of_ae_deriv_le_mul_self
    (C := subcriticalPathConstant d theta (2 * C)) hAC hzero
    (fun t _ => integral_nonneg (fun ω => sq_nonneg _))
  filter_upwards [hderiv] with t ht hmem
  rw [ht hmem]
  exact (integral_tree_density_le_subcritical s hcard hθ0 hθ hsub hC
    (hX t hmem) (hY t hmem) (hInt t hmem) (hH t hmem) (hH' t hmem)
    (hU t hmem) (hlog t hmem)).2

end Probability

end Problem367.ResponseRows

end

end OAI
