import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Second-order block estimates

The finite reductions use the bottom-energy estimate from the binary
manuscript's `lem:second-order` and the unit manuscript's `lem:perturbation`.
Explicit positivity and operator norm bounds give vector and variational
estimates for the penalty, inverse, coupling and high perturbation blocks.

Real inner products also express the real quadratic forms of complex spin
Hilbert spaces by restriction of scalars.
-/

noncomputable section

open scoped InnerProductSpace

namespace ContinuumCoulomb
namespace Perturbation

variable {L H : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℝ L]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def penaltyForm (A : H →L[ℝ] H) (q : H) : ℝ := ⟪q, A q⟫_ℝ

def inverseForm (T : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) : ℝ :=
  ⟪B p, T (B p)⟫_ℝ

/-- Full block energy when the low-low perturbation block vanishes. -/
def blockEnergy (A D : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  penaltyForm A q + 2 * ⟪q, B p⟫_ℝ + ⟪q, D q⟫_ℝ

theorem inverseForm_nonneg (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (hA : ∀ q, 0 ≤ penaltyForm A q) (p : L) :
    0 ≤ inverseForm T B p := by
  have h := hA (T (B p))
  simpa only [penaltyForm, hAT, real_inner_comm, inverseForm] using h

/-- The precise square-completion identity, before any estimates. -/
theorem penalty_square_identity (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (p : L) (q : H) {σ : ℝ} (hσ : σ ≠ 0) :
    σ * penaltyForm A q + 2 * ⟪q, B p⟫_ℝ =
      σ * penaltyForm A (q + σ⁻¹ • T (B p)) - σ⁻¹ * inverseForm T B p := by
  have hcross : ⟪T (B p), A q⟫_ℝ = ⟪q, B p⟫_ℝ := by
    rw [hAsymm, hAT, real_inner_comm]
  simp only [penaltyForm, inverseForm, map_add, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hAT, hcross]
  rw [real_inner_comm (T (B p)) (B p)]
  field_simp
  ring

/-- The trial vector used in the second-order variational upper bound. -/
theorem blockEnergy_trial_identity (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (p : L) :
    blockEnergy A D B p (-(T (B p))) =
      -inverseForm T B p + ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ := by
  simp only [blockEnergy, penaltyForm, inverseForm, map_neg, hAT,
    inner_neg_left, inner_neg_right]
  rw [real_inner_comm (T (B p)) (B p)]
  ring

theorem inverse_coupling_norm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (_hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    ‖T (B p)‖ ≤ ε * ‖p‖ := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    ‖T (B p)‖ ≤ ‖T‖ * ‖B p‖ := T.le_opNorm _
    _ ≤ (1 / g) * (ε * g * ‖p‖) := by
      exact mul_le_mul hT hBp (norm_nonneg _) (by positivity)
    _ = ε * ‖p‖ := by field_simp

theorem inverseForm_le (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (p : L) :
    inverseForm T B p ≤ g * ε ^ 2 * ‖p‖ ^ 2 := by
  have hBp : ‖B p‖ ≤ ε * g * ‖p‖ :=
    (B.le_opNorm p).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hTBp := inverse_coupling_norm_le T B hg hε hT hB p
  calc
    inverseForm T B p ≤ ‖B p‖ * ‖T (B p)‖ := real_inner_le_norm _ _
    _ ≤ (ε * g * ‖p‖) * (ε * ‖p‖) :=
      mul_le_mul hBp hTBp (norm_nonneg _) (by positivity)
    _ = g * ε ^ 2 * ‖p‖ ^ 2 := by ring

theorem highPerturbation_abs_le (D : H →L[ℝ] H)
    {g ε : ℝ} (hD : ‖D‖ ≤ ε * g) (q : H) :
    |⟪q, D q⟫_ℝ| ≤ ε * g * ‖q‖ ^ 2 := by
  calc
    |⟪q, D q⟫_ℝ| ≤ ‖q‖ * ‖D q‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖q‖ * (ε * g * ‖q‖) := by
      exact mul_le_mul_of_nonneg_left
        ((D.le_opNorm q).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
        (norm_nonneg _)
    _ = ε * g * ‖q‖ ^ 2 := by ring

theorem highPerturbation_relative_lower (A D : H →L[ℝ] H)
    {g ε : ℝ} (hε : 0 ≤ ε) (hD : ‖D‖ ≤ ε * g)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q) (q : H) :
    -(ε * penaltyForm A q) ≤ ⟪q, D q⟫_ℝ := by
  have h := (abs_le.mp (highPerturbation_abs_le D hD q)).1
  have hgap' := mul_le_mul_of_nonneg_left (hgap q) hε
  nlinarith

/-- Completing a square lowers the full form by the inverse coupling form. -/
theorem blockEnergy_lower (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hD : ‖D‖ ≤ ε * g) (p : L) (q : H) :
    -inverseForm T B p / (1 - ε) ≤ blockEnergy A D B p q := by
  have hσ : 0 < 1 - ε := by linarith
  have hid := penalty_square_identity A T B hAT hAsymm p q (ne_of_gt hσ)
  have hsquare := mul_nonneg (le_of_lt hσ) (hA (q + (1 - ε)⁻¹ • T (B p)))
  have hDq := highPerturbation_relative_lower A D hε hD hgap q
  unfold blockEnergy
  rw [div_eq_mul_inv]
  nlinarith

def blockRayleigh (A D : H →L[ℝ] H) (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  blockEnergy A D B p q / (‖p‖ ^ 2 + ‖q‖ ^ 2)

def blockBottom (A D : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
    e = blockRayleigh A D B p q}

/-- Pointwise inverse-form control gives the lower Rayleigh bound. -/
theorem blockRayleigh_lower (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hκ : 0 ≤ κ)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hD : ‖D‖ ≤ ε * g)
    (hK : ∀ p, inverseForm T B p ≤ κ * ‖p‖ ^ 2)
    (p : L) (q : H) (hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2) :
    -κ / (1 - ε) ≤ blockRayleigh A D B p q := by
  have hσ : 0 < 1 - ε := by linarith
  have he := blockEnergy_lower A T D B hε hε1 hAT hAsymm hA hgap hD p q
  have hK' := div_le_div_of_nonneg_right (neg_le_neg (hK p)) (le_of_lt hσ)
  have hq : 0 ≤ κ * (1 - ε)⁻¹ * ‖q‖ ^ 2 := by positivity
  unfold blockRayleigh
  apply (le_div_iff₀ hnorm).mpr
  simp only [div_eq_mul_inv] at he hK' ⊢
  nlinarith

theorem cubic_lower_error {g ε κ : ℝ} (hg : 0 < g)
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hκ : κ ≤ g * ε ^ 2) :
    -κ - 2 * g * ε ^ 3 ≤ -κ / (1 - ε) := by
  have hσ : 0 < 1 - ε := by linarith
  have hsmall : 0 ≤ g * ε ^ 3 * (1 - 2 * ε) :=
    mul_nonneg (by positivity) (by linarith)
  have hκ' := mul_le_mul_of_nonneg_left hκ hε
  apply (le_div_iff₀ hσ).mpr
  nlinarith

/-- The explicit second-order trial vector gives a cubic upper error. -/
theorem blockRayleigh_trial_upper (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hκ : κ ≤ g * ε ^ 2)
    (p : L) (hp : ‖p‖ = 1) (hattain : inverseForm T B p = κ) :
    blockRayleigh A D B p (-(T (B p))) ≤ -κ + 2 * g * ε ^ 3 := by
  have hnorm : ‖-(T (B p))‖ ≤ ε := by
    simpa only [norm_neg, hp, mul_one] using inverse_coupling_norm_le T B hg hε hT hB p
  have hr : ‖-(T (B p))‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg (-(T (B p)))]
  have hr0 : 0 ≤ ‖-(T (B p))‖ ^ 2 := sq_nonneg _
  have hd := (abs_le.mp (highPerturbation_abs_le D hD (-(T (B p))))).2
  have hd' : ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ ≤ g * ε ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ ε * g by positivity)
    nlinarith
  have hκr : κ * ‖-(T (B p))‖ ^ 2 ≤ g * ε ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_right hκ hr0
    have h2 := mul_le_mul_of_nonneg_left hr (show 0 ≤ g * ε ^ 2 by positivity)
    nlinarith
  have hε4 : g * ε ^ 4 ≤ g * ε ^ 3 := by
    have h := mul_nonneg (show 0 ≤ g * ε ^ 3 by positivity)
      (show 0 ≤ 1 - ε by linarith)
    nlinarith
  have hden : 0 < 1 + ‖-(T (B p))‖ ^ 2 := by positivity
  unfold blockRayleigh
  rw [blockEnergy_trial_identity A T D B hAT p, hattain, hp, one_pow]
  apply (div_le_iff₀ hden).mpr
  have hcost : 0 ≤ 2 * g * ε ^ 3 * ‖-(T (B p))‖ ^ 2 := by positivity
  nlinarith

/-- Supporting variational second-order estimate for the zero low-low
block case.  The effective positive inverse form is bounded by `κ` and
attains it at the supplied unit vector, exactly as for the maximum
eigenvector of the finite positive matrix `PBA⁻¹BP` in the manuscript. -/
theorem blockBottom_second_order (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε κ : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hK : ∀ p, inverseForm T B p ≤ κ * ‖p‖ ^ 2)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (hattain : inverseForm T B p₀ = κ) :
    |blockBottom A D B + κ| ≤ 2 * g * ε ^ 3 := by
  have hκ0 : 0 ≤ κ := by
    rw [← hattain]
    exact inverseForm_nonneg A T B hAT hA p₀
  have hκ : κ ≤ g * ε ^ 2 := by
    have h := inverseForm_le T B hg hε hT hB p₀
    simpa only [hattain, hp₀, one_pow, mul_one] using h
  have hnorm : 0 < ‖p₀‖ ^ 2 + ‖-(T (B p₀))‖ ^ 2 := by rw [hp₀]; positivity
  have hnonempty :
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q}.Nonempty :=
    ⟨_, p₀, -(T (B p₀)), hnorm, rfl⟩
  have hlower (e : ℝ)
      (he : ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q) : -κ - 2 * g * ε ^ 3 ≤ e := by
    obtain ⟨p, q, hpq, rfl⟩ := he
    exact (cubic_lower_error hg hε hεhalf hκ).trans
      (blockRayleigh_lower A T D B hε (by linarith) hκ0 hAT hAsymm hA hgap hD hK p q hpq)
  have hbdd : BddBelow
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = blockRayleigh A D B p q} := ⟨_, hlower⟩
  have hbottomLower : -κ - 2 * g * ε ^ 3 ≤ blockBottom A D B :=
    le_csInf hnonempty hlower
  have hbottomUpper : blockBottom A D B ≤ -κ + 2 * g * ε ^ 3 :=
    (csInf_le hbdd ⟨p₀, -(T (B p₀)), hnorm, rfl⟩).trans
      (blockRayleigh_trial_upper A T D B hg hε hεhalf hAT hT hB hD hκ p₀ hp₀ hattain)
  apply abs_le.mpr
  constructor <;> linarith

/-- First-order low compression together with its second-order inverse term. -/
def effectiveForm (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) : ℝ := ⟪p, C p⟫_ℝ - inverseForm T B p

theorem effectiveForm_smul (C : L →L[ℝ] L) (T : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    effectiveForm C T B (r • p) = r ^ 2 * effectiveForm C T B p := by
  simp only [effectiveForm, inverseForm, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- Finite dimensionality supplies the effective ground vector; this
is not an additional simulation assumption. -/
theorem effectiveForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧
      ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hc : Continuous (effectiveForm C T B) :=
    (continuous_id.inner C.continuous).sub
      (B.continuous.inner (T.continuous.comp B.continuous))
  have hnonempty : (Metric.sphere (0 : L) 1).Nonempty := ⟨u, by simpa using hu⟩
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sphere (0 : L) 1).exists_isMinOn hnonempty hc.continuousOn
  refine ⟨p, by simpa using hp, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, effectiveForm, inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change effectiveForm C T B p ≤ effectiveForm C T B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [effectiveForm_smul] at h
  calc
    effectiveForm C T B p * ‖x‖ ^ 2 ≤
        (‖x‖⁻¹ ^ 2 * effectiveForm C T B x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = effectiveForm C T B x := by field_simp

def effectiveBottom (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ p : L, ‖p‖ = 1 ∧ e = effectiveForm C T B p}

theorem effectiveBottom_eq (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x) :
    effectiveBottom C T B = effectiveForm C T B p := by
  have hlower (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = effectiveForm C T B x) :
      effectiveForm C T B p ≤ e := by
    obtain ⟨x, hx, rfl⟩ := he
    simpa only [hx, one_pow, mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_, hlower⟩ ⟨p, hp, rfl⟩)
    (le_csInf ⟨_, p, hp, rfl⟩ hlower)

def lowBlockEnergy (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  ⟪p, C p⟫_ℝ + blockEnergy A D B p q

def lowBlockRayleigh (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (q : H) : ℝ :=
  lowBlockEnergy C A D B p q / (‖p‖ ^ 2 + ‖q‖ ^ 2)

def lowBlockBottom (C : L →L[ℝ] L) (A D : H →L[ℝ] H)
    (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
    e = lowBlockRayleigh C A D B p q}

theorem effectiveForm_bounds (C : L →L[ℝ] L) (A T : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε)
    (hAT : ∀ x, A (T x) = x) (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hC : ‖C‖ ≤ ε * g)
    (p : L) :
    -(ε * g + g * ε ^ 2) * ‖p‖ ^ 2 ≤ effectiveForm C T B p ∧
      effectiveForm C T B p ≤ ε * g * ‖p‖ ^ 2 := by
  have hCp := abs_le.mp (highPerturbation_abs_le C hC p)
  have hK0 := inverseForm_nonneg A T B hAT hA p
  have hK := inverseForm_le T B hg hε hT hB p
  unfold effectiveForm
  constructor <;> nlinarith

theorem first_order_inverse_cubic_loss {g ε k r : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hr : 0 ≤ r) (hk : k ≤ g * ε ^ 2 * r) :
    -4 * g * ε ^ 3 * r ≤ k - (1 - 2 * ε)⁻¹ * k := by
  have hσ : 0 < 1 - 2 * ε := by linarith
  have hid : k - (1 - 2 * ε)⁻¹ * k = (-2 * ε * k) / (1 - 2 * ε) := by
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ hσ).mpr
  have h := mul_le_mul_of_nonneg_left hk hε
  have hsmall : 0 ≤ g * ε ^ 3 * r * (1 - 4 * ε) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- A shifted square gives the lower bound even when the first-order
compression is nonzero.  The effective form is only assumed bounded
below pointwise; the full-energy conclusion is proved here. -/
theorem lowBlockEnergy_shift_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμupper : μ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p : L) (q : H) :
    -4 * g * ε ^ 3 * ‖p‖ ^ 2 ≤
      lowBlockEnergy C A D B p q - μ * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hσ : 0 < 1 - 2 * ε := by linarith
  have hid := penalty_square_identity A T B hAT hAsymm p q (ne_of_gt hσ)
  have hsquare := mul_nonneg (le_of_lt hσ) (hA (q + (1 - 2 * ε)⁻¹ • T (B p)))
  have hDq := (abs_le.mp (highPerturbation_abs_le D hD q)).1
  have hμq := mul_le_mul_of_nonneg_right hμupper (sq_nonneg ‖q‖)
  have hgap' := mul_le_mul_of_nonneg_left (hgap q) (show 0 ≤ 2 * ε by positivity)
  have hminp := hmin p
  have hK := inverseForm_le T B hg hε hT hB p
  have hloss := first_order_inverse_cubic_loss hg hε hεquarter (sq_nonneg ‖p‖) hK
  unfold effectiveForm at hminp
  unfold lowBlockEnergy blockEnergy
  nlinarith

theorem lowBlockRayleigh_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμupper : μ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p : L) (q : H) (hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2) :
    μ - 4 * g * ε ^ 3 ≤ lowBlockRayleigh C A D B p q := by
  have hlower := lowBlockEnergy_shift_lower C A T D B hg hε hεquarter hAT hAsymm
    hA hgap hT hB hD hμupper hmin p q
  have hcost : 0 ≤ 4 * g * ε ^ 3 * ‖q‖ ^ 2 := by positivity
  unfold lowBlockRayleigh
  apply (le_div_iff₀ hnorm).mpr
  nlinarith

/-- The same inverse-coupling trial vector works with the unreplaced
low-block terms retained. -/
theorem lowBlockRayleigh_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε)
    (hAT : ∀ x, A (T x) = x)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hμlower : -2 * ε * g ≤ μ)
    (p : L) (hp : ‖p‖ = 1) (hattain : effectiveForm C T B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ + 3 * g * ε ^ 3 := by
  have hnorm : ‖-(T (B p))‖ ≤ ε := by
    simpa only [norm_neg, hp, mul_one] using inverse_coupling_norm_le T B hg hε hT hB p
  have hr : ‖-(T (B p))‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg (-(T (B p)))]
  have hr0 : 0 ≤ ‖-(T (B p))‖ ^ 2 := sq_nonneg _
  have hd := (abs_le.mp (highPerturbation_abs_le D hD (-(T (B p))))).2
  have hμr := mul_le_mul_of_nonneg_right hμlower hr0
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 3 * ε * g by positivity)
  have hden : 0 < 1 + ‖-(T (B p))‖ ^ 2 := by positivity
  have hcost : 0 ≤ 3 * g * ε ^ 3 * ‖-(T (B p))‖ ^ 2 := by positivity
  unfold lowBlockRayleigh lowBlockEnergy
  rw [blockEnergy_trial_identity A T D B hAT p, hp, one_pow]
  unfold effectiveForm at hattain
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Quantitative version of the unit manuscript's `lem:perturbation`,
retaining the nonzero first-order compression.  `μ` is the attained
variational minimum of `C - B* T B`; the full variational bottom is
proved within `4 g ε³` of it. -/
theorem lowBlockBottom_second_order (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g ε μ : ℝ}
    (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g)
    (hC : ‖C‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (hmin : ∀ p, μ * ‖p‖ ^ 2 ≤ effectiveForm C T B p)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (hattain : effectiveForm C T B p₀ = μ) :
    |lowBlockBottom C A D B - μ| ≤ 4 * g * ε ^ 3 := by
  have hbounds := effectiveForm_bounds C A T B hg hε hAT hA hT hB hC p₀
  simp only [hattain, hp₀, one_pow, mul_one] at hbounds
  have hμupper : μ ≤ ε * g := hbounds.2
  have hμlower : -2 * ε * g ≤ μ := by
    have hsmall : 0 ≤ g * ε * (1 - ε) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hbounds.1]
  have hnorm : 0 < ‖p₀‖ ^ 2 + ‖-(T (B p₀))‖ ^ 2 := by rw [hp₀]; positivity
  have hnonempty :
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q}.Nonempty :=
    ⟨_, p₀, -(T (B p₀)), hnorm, rfl⟩
  have hlower (e : ℝ)
      (he : ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q) : μ - 4 * g * ε ^ 3 ≤ e := by
    obtain ⟨p, q, hpq, rfl⟩ := he
    exact lowBlockRayleigh_lower C A T D B hg hε hεquarter hAT hAsymm hA hgap
      hT hB hD hμupper hmin p q hpq
  have hbdd : BddBelow
      {e | ∃ (p : L) (q : H), 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 ∧
        e = lowBlockRayleigh C A D B p q} := ⟨_, hlower⟩
  have hbottomLower : μ - 4 * g * ε ^ 3 ≤ lowBlockBottom C A D B :=
    le_csInf hnonempty hlower
  have hbottomUpper : lowBlockBottom C A D B ≤ μ + 3 * g * ε ^ 3 :=
    (csInf_le hbdd ⟨p₀, -(T (B p₀)), hnorm, rfl⟩).trans
      (lowBlockRayleigh_trial_upper C A T D B hg hε hAT hT hB hD hμlower p₀ hp₀ hattain)
  apply abs_le.mpr
  constructor <;> nlinarith [show 0 ≤ g * ε ^ 3 by positivity]

/-- The finite-dimensional, nonzero-low-block perturbation estimate
compares the two actual variational infima. -/
theorem finite_lowBlockBottom_second_order [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g)
    (hC : ‖C‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (u : L) (hu : ‖u‖ = 1) :
    |lowBlockBottom C A D B - effectiveBottom C T B| ≤ 4 * g * ε ^ 3 := by
  obtain ⟨p, hp, hmin⟩ := effectiveForm_minimizer C T B u hu
  rw [effectiveBottom_eq C T B p hp hmin]
  exact lowBlockBottom_second_order C A T D B hg hε hεquarter hAT hAsymm hA hgap
    hT hB hC hD hmin p hp rfl

/-- The sharper zero-low-block estimate also compares actual variational
infima without a separately supplied effective maximizing vector. -/
theorem finite_blockBottom_second_order [FiniteDimensional ℝ L]
    (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g ε : ℝ} (hg : 0 < g) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (hA : ∀ q, 0 ≤ penaltyForm A q)
    (hgap : ∀ q, g * ‖q‖ ^ 2 ≤ penaltyForm A q)
    (hT : ‖T‖ ≤ 1 / g) (hB : ‖B‖ ≤ ε * g) (hD : ‖D‖ ≤ ε * g)
    (u : L) (hu : ‖u‖ = 1) :
    |blockBottom A D B - effectiveBottom (0 : L →L[ℝ] L) T B| ≤ 2 * g * ε ^ 3 := by
  obtain ⟨p, hp, hmin⟩ := effectiveForm_minimizer (0 : L →L[ℝ] L) T B u hu
  have hK (x : L) : inverseForm T B x ≤ inverseForm T B p * ‖x‖ ^ 2 := by
    have h := hmin x
    simp only [effectiveForm, zero_apply, inner_zero_right, zero_sub] at h
    nlinarith
  have hvalue := effectiveBottom_eq (0 : L →L[ℝ] L) T B p hp hmin
  simp only [effectiveForm, zero_apply, inner_zero_right, zero_sub] at hvalue
  rw [hvalue, sub_neg_eq_add]
  exact blockBottom_second_order A T D B hg hε hεhalf hAT hAsymm hA hgap
    hT hB hD hK p hp rfl

end Perturbation
end ContinuumCoulomb

end

end OAI
