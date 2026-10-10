import OAI.NumberTheory.DukePrimeDegree.Geometry.SublinearHeight

namespace OAI

/-! # Subexponential chart radii along almost every diagonal orbit

Bounded height increments and finite invariant mass give sublinear height
growth by the maximal occupation inequality. Applied to the actual local
injectivity height, this proves the chart control needed in entropy
comparisons without assuming an integrable logarithmic cusp height.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_height_div_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (H (T^[n] x) : ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hbound (q : ℕ) := ae_height_affine_bound μ hT H hH hstep
    (show 0 < 1/(q+1:ℝ) by positivity)
  filter_upwards [ae_all_iff.mpr hbound] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨C,hC⟩ := hx q
  have hlim : Tendsto (fun n : ℕ => (C:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)),eventually_ge_atTop 1]
    with n hn hnone
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hnone
  have hf := div_le_div_of_nonneg_right (hC n) hnp.le
  rw [add_div,mul_div_cancel_right₀ _ hnp.ne'] at hf
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnp.le)]
  linarith

theorem exists_tempered_local_injectivity_height (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) :
    ∃ (κ : ℝ) (H : X (d+1) → ℕ), 1 < κ ∧ Measurable H ∧
      (∀ x, LocalInjectivityAt ((κ⁻¹)^(H x)) x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
        (H ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[n] x) : ℝ)/(n:ℝ))
          atTop (𝓝 0) := by
  obtain ⟨κ,H,hκ,hH,hinj,hstep⟩ := exists_local_injectivity_height ell hell
  have hT : MeasurePreserving
      (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  exact ⟨κ,H,hκ,hH,hinj,ae_height_div_tendsto_zero μ hT H hH (fun x => (hstep x).1)⟩

lemma radius_eventually_ge_exp_of_sublinear {H : ℕ → ℕ} {κ : ℝ} (hκ : 1 < κ)
    (hH : Tendsto (fun n : ℕ => (H n : ℝ)/(n:ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-ε*(n:ℝ)) ≤ (κ⁻¹)^(H n) := by
  have hlog : 0 < Real.log κ := Real.log_pos hκ
  have hκp : 0 < κ := zero_lt_one.trans hκ
  have he : 0 < ε/Real.log κ := div_pos hε hlog
  filter_upwards [hH.eventually (gt_mem_nhds he),eventually_ge_atTop 1] with n hn hnone
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hnone
  have hprod := mul_lt_mul_of_pos_right ((div_lt_iff₀ hnp).mp hn) hlog
  have hcancel : (ε/Real.log κ)*(n:ℝ)*Real.log κ=ε*(n:ℝ) := by
    field_simp
  rw [hcancel] at hprod
  have hpow : 0 < (κ⁻¹)^(H n) := pow_pos (inv_pos.mpr hκp) _
  have hlogpow : Real.log ((κ⁻¹)^(H n)) = -(H n:ℝ)*Real.log κ := by
    rw [Real.log_pow,Real.log_inv]
    ring
  calc
    _ ≤ Real.exp (-(H n:ℝ)*Real.log κ) := Real.exp_le_exp.mpr (by linarith)
    _ = (κ⁻¹)^(H n) := by rw [←hlogpow,Real.exp_log hpow]

/-- Local quotient charts shrink more slowly than every fixed exponential
along almost every diagonal orbit. -/
theorem ae_local_injectivity_subexponential (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      LocalInjectivityAt (Real.exp (-ε*(n:ℝ)))
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[n] x) := by
  obtain ⟨κ,H,hκ,_,hinj,ht⟩ := exists_tempered_local_injectivity_height d μ hA ell hell
  filter_upwards [ht] with x hx
  intro ε hε
  filter_upwards [radius_eventually_ge_exp_of_sublinear hκ hx hε] with n hn
  exact (hinj _).mono hn

end DukePrimeDegree

end

end OAI
