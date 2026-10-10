import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallPrimeSamples

namespace OAI

/-! Absorbing the integer-kernel error at the actual sparse-sample scale. -/
namespace TwoPointCorrelations

open Finset Filter

noncomputable def halaszSparseErrorConstant : ℝ :=
  (440/Real.pi)*Real.sqrt 2 + (512/(2*Real.pi)^2)*halaszIntegerSquareMass

lemma halasz_sparse_error_constant_pos : 0 < halaszSparseErrorConstant := by
  unfold halaszSparseErrorConstant
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg)

lemma halasz_extra_cofactor_length {L N a : ℝ} (hL : 0 ≤ L)
    (hlog : 1000 ≤ Real.log L) (ha : 0 < a)
    (haU : a ≤ Real.exp (L/Real.log L)) (hN : Real.exp L ≤ N) :
    Real.exp ((999/1000:ℝ)*L) ≤ N/a := by
  have hlog0 : 0 < Real.log L := by linarith
  have hq : L/Real.log L ≤ L/1000 :=
    div_le_div_of_nonneg_left hL (by norm_num) hlog
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ Real.exp ((999/1000:ℝ)*L)*Real.exp (L/1000) :=
      mul_le_mul_of_nonneg_left (haU.trans (Real.exp_le_exp.mpr hq)) (Real.exp_pos _).le
    _ = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ N := hN

lemma halasz_no_small_card_budget {L R K : ℝ}
    (hcard : R ≤ K*Real.exp ((99/200:ℝ)*L))
    (hK : K ≤ Real.exp ((3/1000:ℝ)*L)) :
    R ≤ Real.exp ((249/500:ℝ)*L) := by
  calc
    _ ≤ K*Real.exp ((99/200:ℝ)*L) := hcard
    _ ≤ Real.exp ((3/1000:ℝ)*L)*Real.exp ((99/200:ℝ)*L) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma halasz_sparse_error_exponential {L M T : ℝ} (hL : 0 ≤ L)
    (hM : 1 ≤ M) (_hT : 0 ≤ T) (hTU : T ≤ Real.exp L) :
    halaszSparseKernelError M T ≤ halaszSparseErrorConstant * Real.exp (L/2) := by
  have hM0 : 0 < M := by linarith
  have he1 : 1 ≤ Real.exp (L/2) := Real.one_le_exp (by positivity)
  have hroot : Real.sqrt (2*T) ≤ Real.sqrt 2 * Real.exp (L/2) := by
    calc
      _ ≤ Real.sqrt (2*Real.exp L) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num),← Real.exp_half]
  have htail : (512/(M*(2*Real.pi)^2))*halaszIntegerSquareMass ≤
      ((512/(2*Real.pi)^2)*halaszIntegerSquareMass)*Real.exp (L/2) := by
    calc
      _ ≤ (512/(2*Real.pi)^2)*halaszIntegerSquareMass := by
        apply mul_le_mul_of_nonneg_right _ halasz_integer_square_mass_nonneg
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [sq_nonneg (2*Real.pi)]
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg) he1
  unfold halaszSparseKernelError halaszSparseErrorConstant
  nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 440/Real.pi by positivity)]

theorem halasz_sparse_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ M T R : ℝ,
      Real.exp ((999/1000:ℝ)*L) ≤ M → 0 ≤ T → T ≤ Real.exp L →
      0 ≤ R → R ≤ Real.exp ((249/500:ℝ)*L) →
      R*halaszSparseKernelError M T ≤ M := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_ge_atTop (1000*Real.log halaszSparseErrorConstant)] with L hL hc
  intro M T R hM hT hTU hR hRU
  have hM1 : 1 ≤ M := (Real.one_le_exp (by positivity)).trans hM
  have he := halasz_sparse_error_exponential hL hM1 hT hTU
  have hsmall : Real.log halaszSparseErrorConstant ≤ L/1000 := by linarith
  calc
    _ ≤ Real.exp ((249/500:ℝ)*L)*
        (halaszSparseErrorConstant*Real.exp (L/2)) :=
      mul_le_mul hRU he (by
        unfold halaszSparseKernelError
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg)) (by positivity)
    _ = Real.exp (Real.log halaszSparseErrorConstant+(499/500:ℝ)*L) := by
      rw [Real.exp_add,Real.exp_log halasz_sparse_error_constant_pos]
      rw [show (499/500:ℝ)*L=(249/500:ℝ)*L+L/2 by ring,Real.exp_add]
      ring
    _ ≤ Real.exp ((999/1000:ℝ)*L) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ M := hM

/-- The sparse integer energy is uniformly bounded with the strict
square-root margin supplied by the final original prime band. -/
theorem halasz_sparse_cofactor_at_scale :
    ∀ᶠ L : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ (N : ℕ) (a T : ℝ), 1 ≤ a → 2 ≤ (N:ℝ)/a →
      Real.exp ((999/1000:ℝ)*L) ≤ (N:ℝ)/a → 0 ≤ T → T ≤ Real.exp L →
    ∀ S : Finset ℝ, (S.card:ℝ) ≤ Real.exp ((249/500:ℝ)*L) →
      (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤ 297602 := by
  filter_upwards [halasz_sparse_sample_cost] with L hcost
  intro P F hF N a T ha hx hM hT hTU S hS hfreq hsep
  exact halasz_sparse_cofactor_bounded P F hF N ha hx hT S hfreq hsep
    (hcost ((N:ℝ)/a) T S.card hM hT hTU (Nat.cast_nonneg _) hS)

end TwoPointCorrelations

end OAI
