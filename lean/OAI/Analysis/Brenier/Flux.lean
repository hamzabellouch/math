import Mathlib

namespace OAI

/-!
# Weighted finite-dimensional estimates for moving affine cells

These lemmas isolate the algebraic part of the moment and intercept-speed
estimates. They make no assertion about existence or differentiability of cells.
-/

noncomputable section

open scoped BigOperators

namespace Problem358

section WeightedCauchySchwarz

variable {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Weighted Cauchy--Schwarz, in the form needed by the cell moment estimate. -/
theorem weighted_inner_sum_sq_le (s : Finset ι) (m : ι → ℝ)
    (v B : ι → F) (hm : ∀ i ∈ s, 0 < m i) :
    (∑ i ∈ s, inner ℝ (v i) (B i)) ^ 2 ≤
      (∑ i ∈ s, m i * ‖v i‖ ^ 2) *
        (∑ i ∈ s, ‖B i‖ ^ 2 / m i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact mul_nonneg (hm i hi).le (sq_nonneg _)
  · intro i hi
    exact div_nonneg (sq_nonneg _) (hm i hi).le
  · intro i hi
    have h := abs_real_inner_le_norm (v i) (B i)
    have hsq := (sq_le_sq₀ (abs_nonneg (inner ℝ (v i) (B i)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    rw [sq_abs, mul_pow] at hsq
    convert hsq using 1
    field_simp [(hm i hi).ne']

/-- The energy cancellation step, including the zero-energy case. -/
theorem energy_le_of_sq_le_mul {energy bound : ℝ} (he : 0 ≤ energy) (hb : 0 ≤ bound)
    (h : energy ^ 2 ≤ bound * energy) : energy ≤ bound := by
  rcases he.eq_or_lt with he | he
  · subst energy
    exact hb
  · nlinarith

/-- Algebraic intercept-energy estimate from a moment estimate and cell duality.
The geometric work supplies `hdual` and `hmoment`; no inverse bound on a
Laplacian is used here. -/
theorem intercept_energy_le (s : Finset ι) (m r : ι → ℝ) (v B : ι → F)
    {k w : ℝ} (hm : ∀ i ∈ s, 0 < m i) (hk : 0 ≤ k)
    (hspeed : (∑ i ∈ s, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hdual : (∑ i ∈ s, m i * r i ^ 2) =
      -(∑ i ∈ s, inner ℝ (v i) (B i)))
    (hmoment : (∑ i ∈ s, ‖B i‖ ^ 2 / m i) ≤
      k * (∑ i ∈ s, m i * r i ^ 2)) :
    (∑ i ∈ s, m i * r i ^ 2) ≤ k * w ^ 2 := by
  have he : 0 ≤ ∑ i ∈ s, m i * r i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hm i hi).le (sq_nonneg _)
  have hb : 0 ≤ ∑ i ∈ s, ‖B i‖ ^ 2 / m i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hm i hi).le
  apply energy_le_of_sq_le_mul he (mul_nonneg hk (sq_nonneg w))
  calc
    (∑ i ∈ s, m i * r i ^ 2) ^ 2 =
        (∑ i ∈ s, inner ℝ (v i) (B i)) ^ 2 := by rw [hdual, neg_sq]
    _ ≤ (∑ i ∈ s, m i * ‖v i‖ ^ 2) *
        (∑ i ∈ s, ‖B i‖ ^ 2 / m i) := weighted_inner_sum_sq_le s m v B hm
    _ ≤ w ^ 2 * (∑ i ∈ s, ‖B i‖ ^ 2 / m i) :=
      mul_le_mul_of_nonneg_right hspeed hb
    _ ≤ w ^ 2 * (k * (∑ i ∈ s, m i * r i ^ 2)) :=
      mul_le_mul_of_nonneg_left hmoment (sq_nonneg w)
    _ = (k * w ^ 2) * (∑ i ∈ s, m i * r i ^ 2) := by ring

/-- Square-root form of the intercept-speed estimate. -/
theorem intercept_speed_le (s : Finset ι) (m r : ι → ℝ) (v B : ι → F)
    {k w : ℝ} (hm : ∀ i ∈ s, 0 < m i) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hspeed : (∑ i ∈ s, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hdual : (∑ i ∈ s, m i * r i ^ 2) =
      -(∑ i ∈ s, inner ℝ (v i) (B i)))
    (hmoment : (∑ i ∈ s, ‖B i‖ ^ 2 / m i) ≤
      k * (∑ i ∈ s, m i * r i ^ 2)) :
    Real.sqrt (∑ i ∈ s, m i * r i ^ 2) ≤ Real.sqrt k * w := by
  apply (Real.sqrt_le_iff).2
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hw, ?_⟩
  rw [mul_pow, Real.sq_sqrt hk]
  exact intercept_energy_le s m r v B hm hk hspeed hdual hmoment

/-- Symmetry of the vector-valued face coefficients identifies the adjoint
of site motion with the stationary-site moment derivative. -/
theorem symmetric_flux_pairing [Fintype ι] (q : ι → ℝ) (v : ι → F)
    (b : ι → ι → F) (hb : ∀ i j, b i j = b j i) :
    (∑ i, q i * ∑ j, inner ℝ (b i j) (v i - v j)) =
      ∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j) := by
  classical
  have hswap : (∑ i, ∑ j, q i * inner ℝ (b i j) (v j)) =
      ∑ i, ∑ j, q j * inner ℝ (b i j) (v i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hb j i]
  simp only [inner_sub_right, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib,
    inner_sum, inner_smul_right, sub_mul]
  rw [hswap]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;>
    rw [real_inner_comm]

/-- Symmetry of scalar face coefficients gives the mass pairing identity. -/
theorem symmetric_mass_pairing [Fintype ι] (q r : ι → ℝ)
    (g : ι → ι → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, q i * ∑ j, g i j * (r i - r j)) =
      ∑ i, r i * ∑ j, g i j * (q i - q j) := by
  simpa [mul_comm] using
    symmetric_flux_pairing q r g hg

/-- The finite-cell duality identity follows solely from symmetric face
coefficients and the differentiated fixed-mass constraints. -/
theorem fixed_mass_flux_duality [Fintype ι] (q r : ι → ℝ) (v : ι → F)
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hfixed : ∀ i, (∑ j, g i j * (r i - r j)) +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0) :
    (∑ i, r i * ∑ j, g i j * (q i - q j)) =
      -(∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j)) := by
  have hz : (∑ i, q i * ((∑ j, g i j * (r i - r j)) +
      (∑ j, inner ℝ (b i j) (v i - v j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hfixed i, mul_zero]
  simp only [mul_add, Finset.sum_add_distrib] at hz
  rw [symmetric_mass_pairing q r g hg, symmetric_flux_pairing q v b hb] at hz
  linarith

end WeightedCauchySchwarz

/-- Weighted Cauchy--Schwarz for the mass-displacement mixed term. -/
theorem weighted_abs_sqrt_sum_le {ι : Type*} (s : Finset ι)
    (δ γ D : ι → ℝ) (hγ : ∀ i ∈ s, 0 < γ i)
    (hD : ∀ i ∈ s, 0 ≤ D i) :
    (∑ i ∈ s, |δ i| * Real.sqrt (D i)) ≤
      Real.sqrt ((∑ i ∈ s, δ i ^ 2 / γ i) * (∑ i ∈ s, γ i * D i)) := by
  apply Real.le_sqrt_of_sq_le
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact div_nonneg (sq_nonneg _) (hγ i hi).le
  · intro i hi
    exact mul_nonneg (hγ i hi).le (hD i hi)
  · intro i hi
    rw [mul_pow, sq_abs, Real.sq_sqrt (hD i hi)]
    apply le_of_eq
    field_simp [(hγ i hi).ne']

/-- Young's inequality absorbs the mixed square-root term in the stationary
cell displacement estimate. -/
theorem midpoint_displacement_energy_le {A B R : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (h : A / 4 ≤ R ^ 2 * B / 8 + R / 2 * Real.sqrt (A * B)) :
    A ≤ 5 * R ^ 2 * B := by
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  rw [Real.sqrt_mul hA] at h
  have hy : R / 2 * (Real.sqrt A * Real.sqrt B) ≤ A / 8 + R ^ 2 * B / 2 := by
    nlinarith [sq_nonneg (Real.sqrt A - 2 * R * Real.sqrt B)]
  linarith

/-- Elementary arithmetic/geometric mean gap bound without square-root
normalization: the positive geometric mean can be supplied by its square. -/
theorem geometric_mean_gap_bounds {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : 0 < γ) (hγsq : γ ^ 2 = α * β) :
    0 ≤ (α + β) / 2 - γ ∧
      (α + β) / 2 - γ ≤ (α - β) ^ 2 / (8 * γ) := by
  constructor
  · nlinarith [sq_nonneg (α - β)]
  · apply (le_div_iff₀ (by positivity : 0 < 8 * γ)).2
    nlinarith [sq_nonneg (α + β - 2 * γ)]

/-- The contribution of one cell to the aggregate midpoint energy balance. -/
theorem midpoint_cell_energy_balance {α β γ Am Ap D R : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ) (hγsq : γ ^ 2 = α * β)
    (hAm : Am ≤ R ^ 2) (hAp : Ap ≤ R ^ 2)
    (hdiff : |Am - Ap| ≤ 2 * R * Real.sqrt D) :
    (α * Am + β * Ap) / 2 - γ * ((Am + Ap) / 2) ≤
      R ^ 2 * ((α - β) ^ 2 / γ) / 8 +
        R / 2 * (|α - β| * Real.sqrt D) := by
  obtain ⟨hgap0, hgap⟩ := geometric_mean_gap_bounds hα hβ hγ hγsq
  have hmean : (Am + Ap) / 2 ≤ R ^ 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hmean hgap0
  have hsecond := mul_le_mul_of_nonneg_right hgap (sq_nonneg R)
  have hprod : (α - β) * (Am - Ap) ≤ |α - β| * |Am - Ap| := by
    simpa only [abs_mul] using le_abs_self ((α - β) * (Am - Ap))
  have hprod' := mul_le_mul_of_nonneg_left hdiff (abs_nonneg (α - β))
  have hterm : (α - β) / 4 * (Am - Ap) ≤
      R / 2 * (|α - β| * Real.sqrt D) := by nlinarith
  have hfirst' : ((α + β) / 2 - γ) * ((Am + Ap) / 2) ≤
      R ^ 2 * ((α - β) ^ 2 / γ) / 8 := by
    calc
      _ ≤ ((α + β) / 2 - γ) * R ^ 2 := hfirst
      _ ≤ ((α - β) ^ 2 / (8 * γ)) * R ^ 2 := hsecond
      _ = _ := by ring
  calc
    _ = ((α + β) / 2 - γ) * ((Am + Ap) / 2) +
        (α - β) / 4 * (Am - Ap) := by ring
    _ ≤ _ := add_le_add hfirst' hterm

/-- Aggregate midpoint domination and cellwise moment-control bounds imply
the transport-energy estimate used in the uniform `162` moment bound. -/
theorem midpoint_aggregate_transport {ι : Type*} (s : Finset ι)
    (α β γ D Am Ap : ι → ℝ) {R : ℝ}
    (hα : ∀ i ∈ s, 0 ≤ α i) (hβ : ∀ i ∈ s, 0 ≤ β i)
    (hγ : ∀ i ∈ s, 0 < γ i) (hγsq : ∀ i ∈ s, γ i ^ 2 = α i * β i)
    (hD : ∀ i ∈ s, 0 ≤ D i) (hR : 0 ≤ R)
    (hAm : ∀ i ∈ s, Am i ≤ R ^ 2) (hAp : ∀ i ∈ s, Ap i ≤ R ^ 2)
    (hdiff : ∀ i ∈ s, |Am i - Ap i| ≤ 2 * R * Real.sqrt (D i))
    (hdom : (∑ i ∈ s, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
      ∑ i ∈ s, (α i * Am i + β i * Ap i) / 2) :
    (∑ i ∈ s, γ i * D i) ≤
      5 * R ^ 2 * ∑ i ∈ s, (α i - β i) ^ 2 / γ i := by
  have hA : 0 ≤ ∑ i ∈ s, γ i * D i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hγ i hi).le (hD i hi)
  have hB : 0 ≤ ∑ i ∈ s, (α i - β i) ^ 2 / γ i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hγ i hi).le
  apply midpoint_displacement_energy_le hA hB
  have hsplit : (∑ i ∈ s, γ i * ((Am i + Ap i) / 2 + D i / 4)) =
      (∑ i ∈ s, γ i * ((Am i + Ap i) / 2)) +
        (∑ i ∈ s, γ i * D i) / 4 := by
    simp only [mul_add, mul_div_assoc, Finset.sum_add_distrib, Finset.sum_div]
  rw [hsplit] at hdom
  have hdom' : (∑ i ∈ s, γ i * D i) / 4 ≤
      ∑ i ∈ s, ((α i * Am i + β i * Ap i) / 2 -
        γ i * ((Am i + Ap i) / 2)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  calc
    (∑ i ∈ s, γ i * D i) / 4 ≤
        ∑ i ∈ s, ((α i * Am i + β i * Ap i) / 2 -
          γ i * ((Am i + Ap i) / 2)) := hdom'
    _ ≤ ∑ i ∈ s, (R ^ 2 * ((α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * (|α i - β i| * Real.sqrt (D i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact midpoint_cell_energy_balance (hα i hi) (hβ i hi) (hγ i hi)
        (hγsq i hi) (hAm i hi) (hAp i hi) (hdiff i hi)
    _ = R ^ 2 * (∑ i ∈ s, (α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * (∑ i ∈ s, |α i - β i| * Real.sqrt (D i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ R ^ 2 * (∑ i ∈ s, (α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * Real.sqrt ((∑ i ∈ s, γ i * D i) *
          (∑ i ∈ s, (α i - β i) ^ 2 / γ i)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hR (by norm_num))
      rw [mul_comm]
      exact weighted_abs_sqrt_sum_le s (fun i => α i - β i) γ D hγ hD

end Problem358

end

end OAI
