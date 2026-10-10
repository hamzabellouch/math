import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Absorption of small exponential errors by positive ideal widths -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {V J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype J]

/-- Positive coordinate widths give a uniform exponential gain, without
any norm on the abstract Lie algebra. -/
theorem positive_width_coordinate_bound (b : Basis J ℝ V) (cost : J → ℝ)
    {lo r : ℝ} (hlo : ∀ j, lo ≤ cost j) (hr : 0 ≤ r) (v : V) :
    ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤
      Real.exp (-lo * r) * ‖b.equivFun v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b cost r).repr v j| ≤ _
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (norm_le_pi_norm (b.equivFun v) j) (abs_nonneg _) (Real.exp_pos _).le
  exact Real.exp_le_exp.mpr (by nlinarith [hlo j])

/-- The strict gap absorbs the entire error ball, uniformly over its points.
This is the final small-error step for the ideal coordinate of a lift. -/
theorem eventually_positive_width_absorbs (b : Basis J ℝ V) (cost : J → ℝ)
    {lo α : ℝ} (hlo : ∀ j, lo ≤ cost j) (hgap : α < lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, ∀ v : V,
      ‖b.equivFun v‖ ≤ Real.exp ((α + ε r) * r) →
        ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 := by
  filter_upwards [hε.eventually (eventually_lt_nhds (sub_pos.mpr hgap)),
    eventually_ge_atTop (0 : ℝ)] with r he hr v hv
  calc
    _ ≤ Real.exp (-lo * r) * ‖b.equivFun v‖ :=
      positive_width_coordinate_bound b cost hlo hr v
    _ ≤ Real.exp (-lo * r) * Real.exp ((α + ε r) * r) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ = Real.exp ((α + ε r - lo) * r) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr)

/-- A single explicit positive threshold works for every allowed error
sequence and every point satisfying its logarithmic bound. -/
theorem exists_positive_width_absorption_threshold (b : Basis J ℝ V)
    (cost : J → ℝ) {lo U : ℝ} (hlo : 0 < lo) (hcost : ∀ j, lo ≤ cost j)
    (hU : 0 < U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∀ᶠ r in atTop, ∀ v : V,
        ‖b.equivFun v‖ ≤ Real.exp ((U * δ + ε r) * r) →
          ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 := by
  refine ⟨lo / (2 * U), div_pos hlo (by positivity), ?_⟩
  intro δ _ hδ ε hε
  apply eventually_positive_width_absorbs b cost hcost _ ε hε
  have he : U * (lo / (2 * U)) = lo / 2 := by field_simp
  have hle := mul_le_mul_of_nonneg_left hδ hU.le
  rw [he] at hle
  linarith

/-- A fixed polynomial in a small exponential error is still absorbed by
positive widths. The threshold depends on the polynomial degree. -/
theorem eventually_positive_width_absorbs_polynomial
    (b : Basis J ℝ V) (cost : J → ℝ) {lo α K : ℝ} (p : ℕ)
    (hcost : ∀ j, lo ≤ cost j) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hgap : (p : ℝ) * α < lo) (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, ∀ v : V,
      ‖b.equivFun v‖ ≤ K * (1 + Real.exp ((α + ε r) * r)) ^ p →
        ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 := by
  let θ := (lo - (p : ℝ) * α) / (2 * ((p : ℝ) + 1))
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hθ : 0 < θ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hθeq : θ * (2 * ((p : ℝ) + 1)) = lo - (p : ℝ) * α := by
    dsimp [θ]
    field_simp
  have hsmall : (p : ℝ) * (α + θ) - lo < 0 := by nlinarith
  have ht : Tendsto (fun r : ℝ => ((p : ℝ) * (α + θ) - lo) * r) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hsmall).mpr tendsto_id
  have hlim : Tendsto (fun r : ℝ => (K * 2 ^ p) *
      Real.exp (((p : ℝ) * (α + θ) - lo) * r)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp ht).const_mul (K * 2 ^ p)
  filter_upwards [hε.eventually (eventually_lt_nhds hθ),
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (0 : ℝ)] with r he hbound hr v hv
  have hexp : 1 ≤ Real.exp ((α + θ) * r) := Real.one_le_exp (by positivity)
  have hbase : 1 + Real.exp ((α + ε r) * r) ≤ 2 * Real.exp ((α + θ) * r) := by
    have hh : Real.exp ((α + ε r) * r) ≤ Real.exp ((α + θ) * r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  calc
    _ ≤ Real.exp (-lo * r) * ‖b.equivFun v‖ :=
      positive_width_coordinate_bound b cost hcost hr v
    _ ≤ Real.exp (-lo * r) * (K * (2 * Real.exp ((α + θ) * r)) ^ p) := by
      exact mul_le_mul_of_nonneg_left (hv.trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase p) hK)) (Real.exp_pos _).le
    _ = (K * 2 ^ p) * Real.exp (((p : ℝ) * (α + θ) - lo) * r) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      calc
        _ = (K * 2 ^ p) * (Real.exp (-lo * r) * Real.exp ((p : ℝ) * ((α + θ) * r))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 1 := hbound.le

end PolycyclicRecognition

end

end OAI
