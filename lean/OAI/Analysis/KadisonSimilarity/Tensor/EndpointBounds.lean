import OAI.Analysis.KadisonSimilarity.Tensor.TensorWords
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-!
# The endpoint matrix-unit estimate from a supporting projection

For the coefficient tests it suffices to move a self-adjoint supporting
projection across the inner product. This gives the required dimension factor
without invoking the full tracial commutation theorem.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The tensor norm on elementary words is exactly the product of letter norms. -/
theorem norm_tensorWord : ∀ (n : ℕ) (x : Fin n → E),
    ‖tensorWord x‖ = ∏ i, ‖x i‖ := by
  intro n
  induction n with
  | zero =>
    intro x
    change ‖(⟨1⟩ : TensorScalars.{u})‖ = 1
    simp only [ULift.norm_def, norm_one]
  | succ n ih =>
    intro x
    change ‖x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x)‖ = ∏ i, ‖x i‖
    rw [TensorProduct.norm_tmul, ih, Fin.prod_univ_succ]
    rfl

/-- Completion preserves the elementary tensor norm. -/
theorem norm_completedTensorWord {n : ℕ} (x : Fin n → E) :
    ‖completedTensorWord x‖ = ∏ i, ‖x i‖ := by
  change ‖(tensorWord x : UniformSpace.Completion (TensorWord E n))‖ = _
  rw [UniformSpace.Completion.norm_coe, norm_tensorWord]

/-- The normalized matrix-unit bound multiplies over all tensor letters. -/
theorem norm_completedTensorWord_le_matrix_units {n : ℕ} (x : Fin n → E)
    (m : ℝ) (hm : 0 < m) (hx : ∀ i, ‖x i‖ ≤ m ^ (-(1 : ℝ) / 2)) :
    ‖completedTensorWord x‖ ≤ m ^ (-(n : ℝ) / 2) := by
  rw [norm_completedTensorWord]
  calc
    _ ≤ ∏ _ : Fin n, m ^ (-(1 : ℝ) / 2) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx i)
    _ = (m ^ (-(1 : ℝ) / 2)) ^ n := by simp
    _ = m ^ (-(n : ℝ) / 2) := by
      rw [← Real.rpow_mul_natCast hm.le]
      congr 1
      ring

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A supporting projection transfers to the source through an intertwiner. -/
theorem supported_coefficient_eq
    (Y : H →L[ℂ] K) (p : H →L[ℂ] H) (q : K →L[ℂ] K)
    (hq : q.adjoint = q) (hintertwine : q.comp Y = Y.comp p)
    (a : K) (ha : q a = a) (Ω : H) :
    inner ℂ a (Y Ω) = inner ℂ a (Y (p Ω)) := by
  have hsym (x y : K) : inner ℂ (q x) y = inner ℂ x (q y) := by
    simpa only [hq] using (q.adjoint_inner_right x y).symm
  calc
    inner ℂ a (Y Ω) = inner ℂ (q a) (Y Ω) := by rw [ha]
    _ = inner ℂ a (q (Y Ω)) := hsym a (Y Ω)
    _ = inner ℂ a (Y (p Ω)) := by
      rw [show q (Y Ω) = Y (p Ω) from
        congrArg (fun R : H →L[ℂ] K => R Ω) hintertwine]

/-- The norm cost depends on the two supported vectors. In the matrix-unit
application each endpoint vector has norm equal to the inverse square root of
the matrix dimension. -/
theorem norm_supported_coefficient_le
    (Y : H →L[ℂ] K) (p : H →L[ℂ] H) (q : K →L[ℂ] K)
    (hq : q.adjoint = q) (hintertwine : q.comp Y = Y.comp p)
    (a : K) (ha : q a = a) (Ω : H) :
    ‖inner ℂ a (Y Ω)‖ ≤ ‖Y‖ * (‖a‖ * ‖p Ω‖) := by
  rw [supported_coefficient_eq Y p q hq hintertwine a ha Ω]
  calc
    _ ≤ ‖a‖ * ‖Y (p Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖Y‖ * ‖p Ω‖) :=
      mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg a)
    _ = _ := by ring

/-- Combining the supporting projection with the matrix-unit vector norms
produces exactly the exponent used to eliminate long cycles. -/
theorem matrix_unit_endpoint_bound
    (Y : H →L[ℂ] K) (p : H →L[ℂ] H) (q : K →L[ℂ] K)
    (hq : q.adjoint = q) (hintertwine : q.comp Y = Y.comp p)
    (a : K) (ha : q a = a) (Ω : H)
    (m : ℝ) (hm : 0 < m) (k l : ℕ)
    (htest : ‖a‖ ≤ m ^ (-((l : ℝ) + 1) / 2))
    (hsource : ‖p Ω‖ ≤ m ^ (-((k : ℝ) + 1) / 2)) :
    ‖inner ℂ a (Y Ω)‖ ≤ ‖Y‖ * m ^ (-1 - ((k : ℝ) + l) / 2) := by
  calc
    _ ≤ ‖Y‖ * (‖a‖ * ‖p Ω‖) := norm_supported_coefficient_le Y p q hq hintertwine a ha Ω
    _ ≤ ‖Y‖ * (m ^ (-((l : ℝ) + 1) / 2) * m ^ (-((k : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul htest hsource (norm_nonneg _) (by positivity))
        (norm_nonneg Y)
    _ = _ := by
      rw [← Real.rpow_add hm]
      congr 2
      ring

end KadisonSimilarity

end

end OAI
