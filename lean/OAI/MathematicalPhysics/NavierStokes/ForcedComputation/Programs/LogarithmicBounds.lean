import Mathlib

namespace OAI

/-!
# Derivative bounds for the logarithmic clock

This is the analytic calculation in Lemma `bcs:clock` of *Scalar Potentials
and Slow Clocks for Forced Fluid Computation*. It proves the decay of every
time derivative, rather than assuming decay of the reparametrized field.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace ForcedComputation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logarithmicProfile (r : ℕ) (A : ℝ → E) (t : ℝ) : E :=
  (1 + t)⁻¹ ^ r • A (Real.log (1 + t))

def phaseDerivative (r : ℕ) (A : ℝ → E) (s : ℝ) : E :=
  deriv A s - (r : ℝ) • A s

def phaseIter (r : ℕ) (A : ℝ → E) : ℕ → ℝ → E :=
  Nat.rec A (fun n phase => phaseDerivative (r + n) phase)

theorem logarithmicProfile_contDiffAt (r : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) {t : ℝ} (ht : -1 < t) :
    ContDiffAt ℝ ∞ (logarithmicProfile r A) t := by
  have hp : 1 + t ≠ 0 := by linarith
  have hb : ContDiffAt ℝ ∞ (fun s : ℝ => 1 + s) t :=
    contDiffAt_const.add contDiffAt_id
  exact ((hb.inv hp).pow r).smul (hA.contDiffAt.comp t (hb.log hp))

theorem logarithmicProfile_hasDerivAt (r : ℕ) {A : ℝ → E}
    {t : ℝ} (ht : -1 < t) (hA : DifferentiableAt ℝ A (Real.log (1 + t))) :
    HasDerivAt (logarithmicProfile r A)
      (logarithmicProfile (r + 1) (phaseDerivative r A) t) t := by
  have hp : 0 < 1 + t := by linarith
  have hbase := (hasDerivAt_id t).const_add 1
  have hlog := hbase.log hp.ne'
  have hpow := (hbase.inv hp.ne').pow r
  have h := hpow.smul (hA.hasDerivAt.scomp t hlog)
  simp only [Pi.pow_apply, Pi.inv_apply, Function.comp_apply, id_eq] at h
  have hfrac : -(1 : ℝ) / (1 + t) ^ 2 = -((1 + t)⁻¹ ^ 2) := by
    rw [neg_div, one_div, inv_pow]
  rw [hfrac] at h
  convert h using 1
  · rfl
  · cases r with
    | zero => simp [logarithmicProfile, phaseDerivative]
    | succ r =>
      simp only [logarithmicProfile, phaseDerivative, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, one_div, pow_succ,
        smul_sub, smul_smul]
      module

theorem phaseDerivative_smooth (r : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (phaseDerivative r A) := by
  exact (contDiff_infty_iff_deriv.mp hA).2.sub (hA.const_smul (r : ℝ))

theorem phaseIter_smooth (r : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (n : ℕ) : ContDiff ℝ ∞ (phaseIter r A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact phaseDerivative_smooth (r + n) ih

theorem iteratedDeriv_logarithmicProfile (r n : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) {t : ℝ} (ht : -1 < t) :
    iteratedDeriv n (logarithmicProfile r A) t =
      logarithmicProfile (r + n) (phaseIter r A n) t := by
  induction n generalizing t with
  | zero => simp [phaseIter]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (logarithmicProfile r A) =ᶠ[𝓝 t]
        logarithmicProfile (r + n) (phaseIter r A n) :=
      (eventually_gt_nhds ht).mono fun s hs => ih hs
    rw [he.deriv_eq]
    simpa only [phaseIter, Nat.add_assoc] using
      (logarithmicProfile_hasDerivAt (r + n) ht
        ((phaseIter_smooth r hA n).differentiable (by simp) _)).deriv

def HasBoundedTimeDerivatives (A : ℝ → E) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖iteratedDeriv n A s‖ ≤ C

theorem iteratedDeriv_phaseDerivative (r n : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (s : ℝ) :
    iteratedDeriv n (phaseDerivative r A) s =
      iteratedDeriv (n + 1) A s - (r : ℝ) • iteratedDeriv n A s := by
  have hderiv : ContDiff ℝ ∞ (deriv A) := (contDiff_infty_iff_deriv.mp hA).2
  have hd : ContDiffAt ℝ n (deriv A) s := hderiv.contDiffAt.of_le (by simp)
  have ha : ContDiffAt ℝ n (fun s => (r : ℝ) • A s) s :=
    (hA.const_smul (r : ℝ)).contDiffAt.of_le (by simp)
  change iteratedDeriv n (fun t => deriv A t - (r : ℝ) • A t) s = _
  rw [iteratedDeriv_fun_sub hd ha, iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_succ']

theorem phaseDerivative_bounded (r : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (hbound : HasBoundedTimeDerivatives A) :
    HasBoundedTimeDerivatives (phaseDerivative r A) := by
  intro n
  obtain ⟨C, hC, hCbound⟩ := hbound (n + 1)
  obtain ⟨D, hD, hDbound⟩ := hbound n
  refine ⟨C + (r : ℝ) * D, by positivity, fun s => ?_⟩
  rw [iteratedDeriv_phaseDerivative r n hA]
  calc
    _ ≤ ‖iteratedDeriv (n + 1) A s‖ + ‖(r : ℝ) • iteratedDeriv n A s‖ := norm_sub_le _ _
    _ = ‖iteratedDeriv (n + 1) A s‖ + (r : ℝ) * ‖iteratedDeriv n A s‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg r)]
    _ ≤ C + (r : ℝ) * D := add_le_add (hCbound s)
      (mul_le_mul_of_nonneg_left (hDbound s) (Nat.cast_nonneg r))

theorem phaseIter_bounded (r : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (hbound : HasBoundedTimeDerivatives A) (n : ℕ) :
    HasBoundedTimeDerivatives (phaseIter r A n) := by
  induction n with
  | zero => exact hbound
  | succ n ih => exact phaseDerivative_bounded (r + n) (phaseIter_smooth r hA n) ih

/-- Each time derivative gains a full inverse power of physical time. -/
theorem logarithmicProfile_decay (r n : ℕ) {A : ℝ → E}
    (hA : ContDiff ℝ ∞ A) (hbound : HasBoundedTimeDerivatives A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv n (logarithmicProfile r A) t‖ ≤ C * (1 + t)⁻¹ ^ (r + n) := by
  obtain ⟨C, hC, hboundC⟩ := phaseIter_bounded r hA hbound n 0
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [iteratedDeriv_logarithmicProfile r n hA (by linarith), logarithmicProfile,
    norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + t)⁻¹ ^ (r + n))]
  exact (mul_le_mul_of_nonneg_left (hboundC _) (by positivity)).trans_eq (mul_comm _ _)

section Uniform

variable {ι : Type*}

/-- Bounds uniform in the spatial point (or a spatial derivative index). -/
def UniformTimeBounds (A : ι → ℝ → E) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι, ∀ s : ℝ, ‖iteratedDeriv n (A x) s‖ ≤ C

theorem phaseDerivative_uniform (r : ℕ) {A : ι → ℝ → E}
    (hA : ∀ x, ContDiff ℝ ∞ (A x)) (hbound : UniformTimeBounds A) :
    UniformTimeBounds (fun x => phaseDerivative r (A x)) := by
  intro n
  obtain ⟨C, hC, hCbound⟩ := hbound (n + 1)
  obtain ⟨D, hD, hDbound⟩ := hbound n
  refine ⟨C + (r : ℝ) * D, by positivity, fun x s => ?_⟩
  rw [iteratedDeriv_phaseDerivative r n (hA x)]
  calc
    _ ≤ ‖iteratedDeriv (n + 1) (A x) s‖ + ‖(r : ℝ) • iteratedDeriv n (A x) s‖ :=
      norm_sub_le _ _
    _ = ‖iteratedDeriv (n + 1) (A x) s‖ + (r : ℝ) * ‖iteratedDeriv n (A x) s‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg r)]
    _ ≤ C + (r : ℝ) * D := add_le_add (hCbound x s)
      (mul_le_mul_of_nonneg_left (hDbound x s) (Nat.cast_nonneg r))

theorem phaseIter_uniform (r : ℕ) {A : ι → ℝ → E}
    (hA : ∀ x, ContDiff ℝ ∞ (A x)) (hbound : UniformTimeBounds A) (n : ℕ) :
    UniformTimeBounds (fun x => phaseIter r (A x) n) := by
  induction n with
  | zero => exact hbound
  | succ n ih =>
    exact phaseDerivative_uniform (r + n) (fun x => phaseIter_smooth r (hA x) n) ih

theorem logarithmicProfile_uniform_decay (r n : ℕ) {A : ι → ℝ → E}
    (hA : ∀ x, ContDiff ℝ ∞ (A x)) (hbound : UniformTimeBounds A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι, ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv n (logarithmicProfile r (A x)) t‖ ≤
        C * (1 + t)⁻¹ ^ (r + n) := by
  obtain ⟨C, hC, hboundC⟩ := phaseIter_uniform r hA hbound n 0
  refine ⟨C, hC, fun x t ht => ?_⟩
  rw [iteratedDeriv_logarithmicProfile r n (hA x) (by linarith), logarithmicProfile,
    norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + t)⁻¹ ^ (r + n))]
  exact (mul_le_mul_of_nonneg_left (hboundC x _) (by positivity)).trans_eq (mul_comm _ _)

end Uniform

end ForcedComputation

end

end OAI
