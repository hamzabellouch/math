import OAI.Analysis.KadisonKastler.FinitePhases
import OAI.Analysis.KadisonKastler.QuadraticBounds
import Mathlib.Algebra.Order.BigOperators.Expect

namespace OAI

/-!
# Extracting the scalar commutator from randomized rows

Finite Cauchy–Schwarz bounds the two row errors without a factor for the
number of random choices. Together with the scalar commutator estimate
this gives the constant 141 in the amplification argument.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators Topology

noncomputable section

/-- A norm bound with arbitrarily small eventual error passes to any
limit. No choice of a convergent subsequence is needed. -/
theorem norm_limit_le_of_eventually_le_add {J V : Type*} [NormedAddCommGroup V]
    {l : Filter J} [l.NeBot] {f : J → V} {z : V} {C : ℝ}
    (hf : Filter.Tendsto f l (𝓝 z))
    (hC : ∀ ε > 0, ∀ᶠ j in l, ‖f j‖ ≤ C + ε) : ‖z‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact le_of_tendsto hf.norm (hC ε hε)

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteRMS (v : Ω → H) : ℝ := Real.sqrt (𝔼 w, ‖v w‖ ^ 2)

omit [InnerProductSpace ℂ H] in
theorem finiteRMS_nonneg (v : Ω → H) : 0 ≤ finiteRMS v := Real.sqrt_nonneg _

omit [InnerProductSpace ℂ H] in
theorem expect_norm_mul_le_finiteRMS (v w : Ω → H) :
    (𝔼 i, ‖v i‖ * ‖w i‖) ≤ finiteRMS v * finiteRMS w := by
  have hv : 0 ≤ (𝔼 i, ‖v i‖ ^ 2) := expect_nonneg (fun _ _ => sq_nonneg _)
  have hw : 0 ≤ (𝔼 i, ‖w i‖ ^ 2) := expect_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (expect_nonneg (fun _ _ => by positivity))
    (mul_nonneg (finiteRMS_nonneg v) (finiteRMS_nonneg w))).mp
  rw [mul_pow, finiteRMS, finiteRMS, Real.sq_sqrt hv, Real.sq_sqrt hw]
  exact expect_mul_sq_le_sq_mul_sq univ (fun i => ‖v i‖) (fun i => ‖w i‖)

def meanPairing (x : Ω → H →L[ℂ] H) (v w : Ω → H) : ℂ :=
  𝔼 i, inner ℂ (x i (v i)) (w i)

/-- The contraction between the two vectors does not increase the
Cauchy–Schwarz bound for the average pairing. -/
theorem norm_meanPairing_le (x : Ω → H →L[ℂ] H) (hx : ∀ i, ‖x i‖ ≤ 1)
    (v w : Ω → H) : ‖meanPairing x v w‖ ≤ finiteRMS v * finiteRMS w := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (expect_le_expect fun i _ => ?_).trans (expect_norm_mul_le_finiteRMS v w)
  calc
    ‖inner ℂ (x i (v i)) (w i)‖ ≤ ‖x i (v i)‖ * ‖w i‖ := norm_inner_le_norm _ _
    _ ≤ ‖v i‖ * ‖w i‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hx i) (norm_nonneg (v i)))

/-- An average of arbitrary operator-vector pairings satisfies the same
bound when each operator acts with a uniform bound on the chosen vector. -/
theorem norm_mean_operator_pairing_le (x : Ω → H →L[ℂ] H)
    (v w : Ω → H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, ‖x i (v i)‖ ≤ δ * ‖v i‖) :
    ‖meanPairing x v w‖ ≤ δ * (finiteRMS v * finiteRMS w) := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    (𝔼 i, ‖inner ℂ (x i (v i)) (w i)‖) ≤
        𝔼 i, δ * (‖v i‖ * ‖w i‖) := by
      apply expect_le_expect
      intro i _
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _)).trans_eq (mul_assoc _ _ _))
    _ = δ * (𝔼 i, ‖v i‖ * ‖w i‖) := (mul_expect _ _ _).symm
    _ ≤ δ * (finiteRMS v * finiteRMS w) :=
      mul_le_mul_of_nonneg_left (expect_norm_mul_le_finiteRMS v w) hδ

/-- The two row errors and the original scalar commutator estimate give
an explicit bound on the scalar pairing recovered by the rows. -/
theorem randomized_pairing_bound (h : H →L[ℂ] H) (hh : h.IsSymmetric)
    (x : Ω → H →L[ℂ] H) (hx : ∀ i, ‖x i‖ ≤ 1)
    (v w v₀ w₀ : Ω → H) {δ a b : ℝ} (hδ : 0 ≤ δ)
    (hcomm : ∀ i, ‖(h * x i - x i * h) (v i)‖ ≤ δ * ‖v i‖)
    (hv : finiteRMS v ≤ 1) (hw : finiteRMS w ≤ 1)
    (hforward : finiteRMS (fun i => h (v i) - v₀ i) ≤ a)
    (hbackward : finiteRMS (fun i => h (w i) - w₀ i) ≤ b) :
    ‖meanPairing x v w₀ - meanPairing x v₀ w‖ ≤ δ + a + b := by
  have he : meanPairing x v w₀ - meanPairing x v₀ w =
      meanPairing (fun i => h * x i - x i * h) v w -
        meanPairing x v (fun i => h (w i) - w₀ i) +
          meanPairing x (fun i => h (v i) - v₀ i) w := by
    unfold meanPairing
    rw [← expect_sub_distrib, ← expect_sub_distrib, ← expect_add_distrib]
    apply expect_congr rfl
    intro i _
    simp only [sub_apply, mul_apply_eq_comp, inner_sub_left, map_sub, inner_sub_right,
      hh.apply_clm]
    ring
  have hab : 0 ≤ a ∧ 0 ≤ b :=
    ⟨(finiteRMS_nonneg _).trans hforward, (finiteRMS_nonneg _).trans hbackward⟩
  have h₁ : ‖meanPairing (fun i => h * x i - x i * h) v w‖ ≤ δ := by
    apply (norm_mean_operator_pairing_le _ v w hδ hcomm).trans
    have hprod : finiteRMS v * finiteRMS w ≤ 1 :=
      (mul_le_mul hv hw (finiteRMS_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hδ
  have h₂ : ‖meanPairing x v (fun i => h (w i) - w₀ i)‖ ≤ b := by
    apply (norm_meanPairing_le x hx _ _).trans
    exact (mul_le_mul hv hbackward (finiteRMS_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h₃ : ‖meanPairing x (fun i => h (v i) - v₀ i) w‖ ≤ a := by
    apply (norm_meanPairing_le x hx _ _).trans
    exact (mul_le_mul hforward hw (finiteRMS_nonneg _) hab.1).trans_eq (mul_one _)
  rw [he]
  calc
    _ ≤ (‖meanPairing (fun i => h * x i - x i * h) v w‖ +
        ‖meanPairing x v (fun i => h (w i) - w₀ i)‖) +
          ‖meanPairing x (fun i => h (v i) - v₀ i) w‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ δ + a + b := by linarith

/-- The constants used by the manuscript: two errors of size `70δ`
and one scalar commutator of size `δ`. -/
theorem randomized_pairing_le_one_forty_one (h : H →L[ℂ] H) (hh : h.IsSymmetric)
    (x : Ω → H →L[ℂ] H) (hx : ∀ i, ‖x i‖ ≤ 1)
    (v w v₀ w₀ : Ω → H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcomm : ∀ i, ‖(h * x i - x i * h) (v i)‖ ≤ δ * ‖v i‖)
    (hv : finiteRMS v ≤ 1) (hw : finiteRMS w ≤ 1)
    (hforward : finiteRMS (fun i => h (v i) - v₀ i) ≤ 70 * δ)
    (hbackward : finiteRMS (fun i => h (w i) - w₀ i) ≤ 70 * δ) :
    ‖meanPairing x v w₀ - meanPairing x v₀ w‖ ≤ 141 * δ := by
  have ht := randomized_pairing_bound h hh x hx v w v₀ w₀ hδ hcomm hv hw hforward hbackward
  linarith

/-- The randomized pairing estimate needs only eventual row-error
bounds, as supplied by the clipped-coefficient limits. -/
theorem randomized_pairing_limit_le {J : Type*} {l : Filter J} [l.NeBot]
    (h : H →L[ℂ] H) (hh : h.IsSymmetric)
    (x : J → Ω → H →L[ℂ] H) (hx : ∀ j i, ‖x j i‖ ≤ 1)
    (v w v₀ w₀ : J → Ω → H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcomm : ∀ j i, ‖(h * x j i - x j i * h) (v j i)‖ ≤ δ * ‖v j i‖)
    (hv : ∀ j, finiteRMS (v j) ≤ 1) (hw : ∀ j, finiteRMS (w j) ≤ 1)
    (hforward : ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun i => h (v j i) - v₀ j i) ≤ 70 * δ + ε)
    (hbackward : ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun i => h (w j i) - w₀ j i) ≤ 70 * δ + ε)
    {z : ℂ} (hz : Filter.Tendsto
      (fun j => meanPairing (x j) (v j) (w₀ j) - meanPairing (x j) (v₀ j) (w j)) l (𝓝 z)) :
    ‖z‖ ≤ 141 * δ := by
  apply norm_limit_le_of_eventually_le_add hz
  intro ε hε
  filter_upwards [hforward (ε / 2) (by positivity), hbackward (ε / 2) (by positivity)] with j hj hk
  have hb := randomized_pairing_bound h hh (x j) (hx j) (v j) (w j) (v₀ j) (w₀ j)
    hδ (hcomm j) (hv j) (hw j) hj hk
  linarith

/-- The scalar lower bound in the recovery construction turns the
complex pairing bound into the required real quadratic-form bound. -/
theorem scalar_recovery_quadratic_bound {c d δ : ℝ}
    (hc : 1 / 2 ≤ c) (hbound : ‖((c * d : ℝ) : ℂ)‖ ≤ 141 * δ) :
    |d| ≤ 282 * δ := by
  have hc0 : 0 ≤ c := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0] at hbound
  nlinarith [abs_nonneg d]

end

end KadisonKastler

end OAI
