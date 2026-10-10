import OAI.NumberTheory.DukePrimeDegree.Geometry.TemperedChartRadius
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

/-! # Compact logarithmic balls and a tempered exhaustion

Logarithmic matrix-length sublevels are compact. Their quotient images
control closed logarithmic-distance balls. A rescaled distance from one
fixed point then gives a proper measurable natural height with sublinear
growth under a measure-preserving right translation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem isCompact_matrixLogLength_sublevel {n : ℕ} (R : ℝ) :
    IsCompact {g : G n | matrixLogLength g ≤ R} := by
  have hK := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
    (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℝ) (Real.exp R-1))
  apply hK.of_isClosed_subset (isClosed_le (continuous_matrixLogLength n) continuous_const)
  intro g hg
  change dist g.val 1 ≤ Real.exp R-1
  rw [dist_eq_norm]
  exact (norm_sub_one_le_exp_matrixLogLength g).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hg) 1)

theorem isCompact_quotientLogDistance_sublevel {n : ℕ} (x : X n) (R : ℝ) :
    IsCompact {y : X n | quotientLogDistance x y ≤ R} := by
  have hK := (isCompact_matrixLogLength_sublevel (n := n) (R+1)).image
    (continuous_rightOrbit n x)
  apply hK.of_isClosed_subset (isClosed_le (continuous_quotientLogDistance n x) continuous_const)
  intro y hy
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x y (by norm_num : (0:ℝ)<1)
  exact ⟨g,hlen.le.trans (by linarith [show quotientLogDistance x y ≤ R from hy]),hg⟩

/-- A proper height with two-sided bounded increments under the fixed
right translation. -/
theorem exists_compact_height_bounded_step {n : ℕ} (a : G n) :
    ∃ H : X n → ℕ, Measurable H ∧ (∀ m, IsCompact {x | H x ≤ m}) ∧
      ∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1 := by
  let x₀ : X n := Quotient.mk _ (1 : G n)
  let B := 1+matrixLogLength a
  have hB : 0 < B := by dsimp [B]; linarith [matrixLogLength_nonneg a]
  let f : X n → ℝ := fun x => quotientLogDistance x₀ x/B
  let H : X n → ℕ := fun x => ⌈f x⌉₊
  have hfm : Measurable f := (continuous_quotientLogDistance n x₀).measurable.div_const B
  have hHm : Measurable H := hfm.nat_ceil
  have hstep (b : G n) (hb : matrixLogLength b ≤ matrixLogLength a) (x : X n) : H (rightAction x b) ≤ H x+1 := by
    apply Nat.ceil_le.mpr
    have hd := (abs_le.mp (quotientLogDistance_right_bound x₀ x b)).2
    have hf : f (rightAction x b) ≤ f x+1 := by
      dsimp [f]
      apply (div_le_iff₀ hB).mpr
      have he : (quotientLogDistance x₀ x/B+1)*B = quotientLogDistance x₀ x+B := by
        field_simp
      rw [he]
      dsimp [B]
      linarith
    have hc := Nat.le_ceil (f x)
    change f (rightAction x b) ≤ ((H x+1:ℕ):ℝ)
    push_cast
    exact hf.trans (add_le_add hc le_rfl)
  refine ⟨H,hHm,?_,?_⟩
  · intro m
    have he : {x | H x ≤ m} = {x | quotientLogDistance x₀ x ≤ B*m} := by
      ext x
      change ⌈quotientLogDistance x₀ x/B⌉₊ ≤ m ↔ _
      rw [Nat.ceil_le,div_le_iff₀ hB]
      rw [mul_comm]
      rfl
    rw [he]
    exact isCompact_quotientLogDistance_sublevel x₀ (B*m)
  · intro x
    refine ⟨hstep a le_rfl x,?_⟩
    have hb : matrixLogLength a⁻¹ ≤ matrixLogLength a := by rw [matrixLogLength_inv]
    simpa only [rightAction_mul,mul_inv_cancel,rightAction_one] using
      hstep a⁻¹ hb (rightAction x a)

theorem exists_tempered_compact_exhaustion {n : ℕ}
    (μ : Measure (X n)) [IsFiniteMeasure μ] (a : G n)
    (ha : MeasurePreserving (fun x => rightAction x a) μ μ) :
    ∃ H : X n → ℕ, Measurable H ∧ (∀ m, IsCompact {x | H x ≤ m}) ∧
      ∀ᵐ x ∂μ, Tendsto (fun k : ℕ =>
        (H ((fun y => rightAction y a)^[k] x) : ℝ)/(k:ℝ)) atTop (𝓝 0) := by
  obtain ⟨H,hH,hK,hstep⟩ := exists_compact_height_bounded_step a
  exact ⟨H,hH,hK,ae_height_div_tendsto_zero μ ha H hH (fun x => (hstep x).1)⟩

end DukePrimeDegree

end

end OAI
