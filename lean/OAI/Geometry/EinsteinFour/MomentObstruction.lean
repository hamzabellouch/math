import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

namespace OAI

/-! A direct polynomial proof of the manuscript's two-constrained-moments
obstruction. The variable `x` is `sqrt(z/2)`. Four rational interval
certificates replace the compact-measure optimization argument. -/

namespace PositiveEinsteinFour.MomentObstruction

open MeasureTheory Filter

noncomputable section

def rootWeight (x : ℝ) : ℝ := 1 + x ^ 4 / 10 - x ^ 8 / 72
def rootMoment (x : ℝ) : ℝ := x * rootWeight x
def constraint (x : ℝ) : ℝ := 56 * x ^ 2 + 24 * x ^ 4 - 25
def potential (x : ℝ) : ℝ := 32 * rootMoment x ^ 2 + 18 * x ^ 2 - 36 * x ^ 4
def lowerPolynomial (x : ℝ) : ℝ := 32 * rootWeight x ^ 2 + 18 - 52 * x ^ 2
def dualPolynomial (x : ℝ) : ℝ :=
  (33 / 50) * rootMoment x * constraint x - (403 / 2000) * constraint x -
    (33 / 50) ^ 2 * constraint x ^ 2 / 128 + 18 * x ^ 2 - 36 * x ^ 4

private theorem lower_cert {x : ℝ} (hlo : 0 ≤ x)
    (hhi : x ≤ 1) : 0 ≤ lowerPolynomial x := by
  have hz : 0 ≤ x := by linarith
  have hw : 0 ≤ 1 - x := by linarith
  have hcert : 4050 * (lowerPolynomial x) =
      202500 * (1 - x) ^ 16 +
      3240000 * (x) * (1 - x) ^ 15 +
      24089400 * (x) ^ 2 * (1 - x) ^ 14 +
      110451600 * (x) ^ 3 * (1 - x) ^ 13 +
      349411320 * (x) ^ 4 * (1 - x) ^ 12 +
      808172640 * (x) ^ 5 * (1 - x) ^ 11 +
      1412520120 * (x) ^ 6 * (1 - x) ^ 10 +
      1900681200 * (x) ^ 7 * (1 - x) ^ 9 +
      1986571296 * (x) ^ 8 * (1 - x) ^ 8 +
      1614331008 * (x) ^ 9 * (1 - x) ^ 7 +
      1013073768 * (x) ^ 10 * (1 - x) ^ 6 +
      483298416 * (x) ^ 11 * (1 - x) ^ 5 +
      170408160 * (x) ^ 12 * (1 - x) ^ 4 +
      42313536 * (x) ^ 13 * (1 - x) ^ 3 +
      6779448 * (x) ^ 14 * (1 - x) ^ 2 +
      582768 * (x) ^ 15 * (1 - x) +
      15181 * (x) ^ 16 := by
    unfold lowerPolynomial rootWeight
    ring
  have hp : 0 ≤ 4050 * (lowerPolynomial x) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_0 {x : ℝ} (hlo : 0 ≤ x)
    (hhi : x ≤ 1 / 4) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 0 := by linarith
  have hw : 0 ≤ 1 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      729946521600 * (1 - 4 * x) ^ 13 +
      8451214540800 * (4 * x - 0) * (1 - 4 * x) ^ 12 +
      44734253629440 * (4 * x - 0) ^ 2 * (1 - 4 * x) ^ 11 +
      143206668042240 * (4 * x - 0) ^ 3 * (1 - 4 * x) ^ 10 +
      308991546703872 * (4 * x - 0) ^ 4 * (1 - 4 * x) ^ 9 +
      473869170229248 * (4 * x - 0) ^ 5 * (1 - 4 * x) ^ 8 +
      530527271067648 * (4 * x - 0) ^ 6 * (1 - 4 * x) ^ 7 +
      438134994247680 * (4 * x - 0) ^ 7 * (1 - 4 * x) ^ 6 +
      266251826545920 * (4 * x - 0) ^ 8 * (1 - 4 * x) ^ 5 +
      117245650856032 * (4 * x - 0) ^ 9 * (1 - 4 * x) ^ 4 +
      36244155273088 * (4 * x - 0) ^ 10 * (1 - 4 * x) ^ 3 +
      7423076447728 * (4 * x - 0) ^ 11 * (1 - 4 * x) ^ 2 +
      900827489760 * (4 * x - 0) ^ 12 * (1 - 4 * x) +
      49052866775 * (4 * x - 0) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_1 {x : ℝ} (hlo : 1 / 4 ≤ x)
    (hhi : x ≤ 1 / 2) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 1 := by linarith
  have hw : 0 ≤ 2 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      49052866775 * (2 - 4 * x) ^ 13 +
      374547046390 * (4 * x - 1) * (2 - 4 * x) ^ 12 +
      1107711127288 * (4 * x - 1) ^ 2 * (2 - 4 * x) ^ 11 +
      1478028461488 * (4 * x - 1) ^ 3 * (2 - 4 * x) ^ 10 +
      1147777822832 * (4 * x - 1) ^ 4 * (2 - 4 * x) ^ 9 +
      4322397070176 * (4 * x - 1) ^ 5 * (2 - 4 * x) ^ 8 +
      17544214841088 * (4 * x - 1) ^ 6 * (2 - 4 * x) ^ 7 +
      37665583093248 * (4 * x - 1) ^ 7 * (2 - 4 * x) ^ 6 +
      49210071833856 * (4 * x - 1) ^ 8 * (2 - 4 * x) ^ 5 +
      41997049303552 * (4 * x - 1) ^ 9 * (2 - 4 * x) ^ 4 +
      23754829223936 * (4 * x - 1) ^ 10 * (2 - 4 * x) ^ 3 +
      8639408795648 * (4 * x - 1) ^ 11 * (2 - 4 * x) ^ 2 +
      1837678284800 * (4 * x - 1) ^ 12 * (2 - 4 * x) +
      174322229248 * (4 * x - 1) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_2 {x : ℝ} (hlo : 1 / 2 ≤ x)
    (hhi : x ≤ 3 / 4) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 2 := by linarith
  have hw : 0 ≤ 3 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      174322229248 * (3 - 4 * x) ^ 13 +
      2694699675648 * (4 * x - 2) * (3 - 4 * x) ^ 12 +
      18923665485824 * (4 * x - 2) ^ 2 * (3 - 4 * x) ^ 11 +
      80014357612544 * (4 * x - 2) ^ 3 * (3 - 4 * x) ^ 10 +
      227502921216512 * (4 * x - 2) ^ 4 * (3 - 4 * x) ^ 9 +
      459761839310592 * (4 * x - 2) ^ 5 * (3 - 4 * x) ^ 8 +
      679967974467072 * (4 * x - 2) ^ 6 * (3 - 4 * x) ^ 7 +
      745642437426432 * (4 * x - 2) ^ 7 * (3 - 4 * x) ^ 6 +
      606556136015712 * (4 * x - 2) ^ 8 * (3 - 4 * x) ^ 5 +
      361621098249552 * (4 * x - 2) ^ 9 * (3 - 4 * x) ^ 4 +
      153606171085104 * (4 * x - 2) ^ 10 * (3 - 4 * x) ^ 3 +
      44020313581224 * (4 * x - 2) ^ 11 * (3 - 4 * x) ^ 2 +
      7626516539478 * (4 * x - 2) ^ 12 * (3 - 4 * x) +
      602961182133 * (4 * x - 2) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_3 {x : ℝ} (hlo : 3 / 4 ≤ x)
    (hhi : x ≤ 1) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 3 := by linarith
  have hw : 0 ≤ 4 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      602961182133 * (4 - 4 * x) ^ 13 +
      8050474195980 * (4 * x - 3) * (4 - 4 * x) ^ 12 +
      49107805459248 * (4 * x - 3) ^ 2 * (4 - 4 * x) ^ 11 +
      181015545999936 * (4 * x - 3) ^ 3 * (4 - 4 * x) ^ 10 +
      449173478536992 * (4 * x - 3) ^ 4 * (4 - 4 * x) ^ 9 +
      790669096672896 * (4 * x - 3) ^ 5 * (4 - 4 * x) ^ 8 +
      1012687566317568 * (4 * x - 3) ^ 6 * (4 - 4 * x) ^ 7 +
      951233732886528 * (4 * x - 3) ^ 7 * (4 - 4 * x) ^ 6 +
      650650258538496 * (4 * x - 3) ^ 8 * (4 - 4 * x) ^ 5 +
      316275247562752 * (4 * x - 3) ^ 9 * (4 - 4 * x) ^ 4 +
      103840494911488 * (4 * x - 3) ^ 10 * (4 - 4 * x) ^ 3 +
      20745409527808 * (4 * x - 3) ^ 11 * (4 - 4 * x) ^ 2 +
      1936726425600 * (4 * x - 3) ^ 12 * (4 - 4 * x) +
      9784524800 * (4 * x - 3) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem potential_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    16 * x ^ 4 ≤ potential x := by
  have h := mul_nonneg (sq_nonneg x) (lower_cert hx hx1)
  have hid : potential x - 16 * x ^ 4 = x ^ 2 * lowerPolynomial x := by
    unfold potential rootMoment lowerPolynomial
    ring
  linarith

theorem dual_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / 100 ≤ dualPolynomial x := by
  by_cases h1 : x ≤ 1 / 4
  · linarith [dual_cert_0 hx h1]
  by_cases h2 : x ≤ 1 / 2
  · linarith [dual_cert_1 (by linarith) h2]
  by_cases h3 : x ≤ 3 / 4
  · linarith [dual_cert_2 (by linarith) h3]
  · linarith [dual_cert_3 (by linarith) hx1]

theorem rootMoment_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ rootMoment x := by
  have h8 : x ^ 8 ≤ 1 := pow_le_one₀ hx hx1
  have hr : 0 ≤ rootWeight x := by
    unfold rootWeight
    nlinarith [pow_nonneg hx 4]
  exact mul_nonneg hx hr

/-- The pointwise dual inequality, uniform in the scalar mean parameter. -/
theorem dual_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (t : ℝ) :
    1 / 100 ≤ potential x - 64 * t * rootMoment x + 32 * t ^ 2 +
      ((33 / 50) * t - 403 / 2000) * constraint x := by
  have hid : potential x - 64 * t * rootMoment x + 32 * t ^ 2 +
      ((33 / 50) * t - 403 / 2000) * constraint x =
      32 * (t - rootMoment x + (33 / 50) * constraint x / 64) ^ 2 +
        dualPolynomial x := by
    unfold potential dualPolynomial
    ring
  rw [hid]
  nlinarith [sq_nonneg (t - rootMoment x + (33 / 50) * constraint x / 64),
    dual_lower hx hx1]

private theorem integrable_comp_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {x : Ω → ℝ}
    (hxm : AEStronglyMeasurable x μ) (hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun ω => f (x ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const C).mono' (hf.comp_aestronglyMeasurable hxm)
    (hx.mono fun ω hω => hC (x ω) hω)

/-- The two-moment obstruction in the coordinate `x = sqrt(z/2)`. The proof
uses the explicit dual polynomial; no compactness or extremal-support input
is assumed. -/
theorem normalized_moment_obstruction {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x : Ω → ℝ}
    (hxm : AEStronglyMeasurable x μ) (hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1)
    (hgap : 1 ≤ ∫ ω, 4 * x ω ^ 4 ∂μ)
    (hconstraint : (∫ ω, constraint (x ω) ∂μ) ≤ 0) :
    32 * (∫ ω, rootMoment (x ω) ∂μ) ^ 2 - ∫ ω, potential (x ω) ∂μ < 0 := by
  let t : ℝ := ∫ ω, rootMoment (x ω) ∂μ
  have ih : Integrable (fun ω => rootMoment (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold rootMoment rootWeight; fun_prop)
  have ip : Integrable (fun ω => potential (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold potential rootMoment rootWeight; fun_prop)
  have ig : Integrable (fun ω => constraint (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold constraint; fun_prop)
  have i4 : Integrable (fun ω => x ω ^ 4) μ :=
    integrable_comp_interval (f := fun r : ℝ => r ^ 4) hxm hx (by fun_prop)
  have ht : 0 ≤ t := integral_nonneg_of_ae
    (hx.mono fun ω hω => rootMoment_nonneg hω.1 hω.2)
  have hp : 4 ≤ ∫ ω, potential (x ω) ∂μ := by
    have hlower := integral_mono_ae (i4.const_mul 16) ip
      (hx.mono fun ω hω => potential_lower hω.1 hω.2)
    rw [integral_const_mul] at hgap hlower
    linarith
  by_contra! hJ
  have ht3 : 1 / 3 ≤ t := by
    change 0 ≤ 32 * t ^ 2 - _ at hJ
    nlinarith
  let a : ℝ := (33 / 50) * t - 403 / 2000
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have iF : Integrable (fun ω => potential (x ω) - 64 * t * rootMoment (x ω) +
      32 * t ^ 2 + a * constraint (x ω)) μ :=
    ((ip.sub (ih.const_mul (64 * t))).add (integrable_const (32 * t ^ 2))).add (ig.const_mul a)
  have hF := integral_mono_ae (integrable_const (1 / 100 : ℝ)) iF
    (hx.mono fun ω hω => dual_bound hω.1 hω.2 t)
  have hI : (∫ ω, potential (x ω) - 64 * t * rootMoment (x ω) +
      32 * t ^ 2 + a * constraint (x ω) ∂μ) =
      (∫ ω, potential (x ω) ∂μ) - 32 * t ^ 2 +
        a * ∫ ω, constraint (x ω) ∂μ := by
    have hi1 := integral_add ((ip.sub (ih.const_mul (64 * t))).add
      (integrable_const (32 * t ^ 2))) (ig.const_mul a)
    have hi2 := integral_add (ip.sub (ih.const_mul (64 * t))) (integrable_const (32 * t ^ 2))
    have hi3 := integral_sub ip (ih.const_mul (64 * t))
    simp only [Pi.add_apply, Pi.sub_apply] at hi1 hi2 hi3
    rw [hi1, hi2, hi3]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    change (∫ ω, potential (x ω) ∂μ) - 64 * t * t + 32 * t ^ 2 +
      a * ∫ ω, constraint (x ω) ∂μ = _
    ring
  rw [hI] at hF
  simp only [integral_const, probReal_univ, one_smul] at hF
  have hneg := mul_nonpos_of_nonneg_of_nonpos ha hconstraint
  dsimp [t] at hF
  linarith

/-- The scalar test function in the manuscript. -/
def H (z : ℝ) : ℝ := Real.sqrt z * (1 + z ^ 2 / 40 - z ^ 4 / 1152)

def Phi (z : ℝ) : ℝ := 16 * H z ^ 2 + 9 * z * (1 - z)

theorem H_two_mul_sq {x : ℝ} (hx : 0 ≤ x) :
    H (2 * x ^ 2) = Real.sqrt 2 * rootMoment x := by
  unfold H rootMoment rootWeight
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hx]
  ring

theorem Phi_two_mul_sq {x : ℝ} (hx : 0 ≤ x) :
    Phi (2 * x ^ 2) = potential x := by
  unfold Phi
  rw [H_two_mul_sq hx, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold potential
  ring

/-- The original two-constrained-moments lemma, with no regularity beyond
measurability of the bounded scalar variable. -/
theorem two_constrained_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → ℝ}
    (hzm : AEStronglyMeasurable z μ) (hz : ∀ᵐ ω ∂μ, z ω ∈ Set.Icc (0 : ℝ) 2)
    (hgap : 1 ≤ ∫ ω, z ω ^ 2 ∂μ)
    (hconstraint : (∫ ω, 28 * z ω + 6 * z ω ^ 2 ∂μ) ≤ 25) :
    16 * (∫ ω, H (z ω) ∂μ) ^ 2 - ∫ ω, Phi (z ω) ∂μ < 0 := by
  let x : Ω → ℝ := fun ω => Real.sqrt (z ω / 2)
  have hxm : AEStronglyMeasurable x μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      ((continuous_id.div_const (2 : ℝ)).comp_aestronglyMeasurable hzm)
  have hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hz] with ω hω
    exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).2 (by linarith [hω.2])⟩
  have heq : ∀ᵐ ω ∂μ, z ω = 2 * x ω ^ 2 := by
    filter_upwards [hz] with ω hω
    dsimp [x]
    rw [Real.sq_sqrt (by linarith [hω.1] : 0 ≤ z ω / 2)]
    ring
  have hgap' : 1 ≤ ∫ ω, 4 * x ω ^ 4 ∂μ := by
    have hid : (fun ω => z ω ^ 2) =ᵐ[μ] fun ω => 4 * x ω ^ 4 := by
      filter_upwards [heq] with ω hω
      rw [hω]
      ring
    rwa [integral_congr_ae hid] at hgap
  have ig : Integrable (fun ω => constraint (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold constraint; fun_prop)
  have hconstraint' : (∫ ω, constraint (x ω) ∂μ) ≤ 0 := by
    have hid : (fun ω => 28 * z ω + 6 * z ω ^ 2) =ᵐ[μ]
        fun ω => constraint (x ω) + 25 := by
      filter_upwards [heq] with ω hω
      rw [hω]
      unfold constraint
      ring
    rw [integral_congr_ae hid, integral_add ig (integrable_const _)] at hconstraint
    simp only [integral_const, probReal_univ, one_smul] at hconstraint
    linarith
  have hmain := normalized_moment_obstruction hxm hx hgap' hconstraint'
  have hH : (fun ω => H (z ω)) =ᵐ[μ]
      fun ω => Real.sqrt 2 * rootMoment (x ω) := by
    filter_upwards [heq, hx] with ω hω hxω
    rw [hω, H_two_mul_sq hxω.1]
  have hPhi : (fun ω => Phi (z ω)) =ᵐ[μ] fun ω => potential (x ω) := by
    filter_upwards [heq, hx] with ω hω hxω
    rw [hω, Phi_two_mul_sq hxω.1]
  rw [integral_congr_ae hH, integral_congr_ae hPhi, integral_const_mul, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [hmain]

end

end PositiveEinsteinFour.MomentObstruction

end OAI
