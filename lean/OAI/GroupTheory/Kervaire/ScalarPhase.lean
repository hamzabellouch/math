import OAI.GroupTheory.Kervaire.SpectralLogarithm

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

theorem phase_nonneg (z : ℂ) : 0 ≤ phase z := Int.fract_nonneg _

theorem phase_lt_one (z : ℂ) : phase z < 1 := Int.fract_lt_one _

theorem measurable_phase : Measurable phase :=
  (Complex.measurable_arg.div_const _).fract

theorem phase_exp (x : ℝ) :
    phase (Complex.exp (x * Complex.I)) = Int.fract (x / (2 * Real.pi)) := by
  rw [phase, Complex.arg_exp_mul_I]
  apply Int.fract_eq_fract.mpr
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  rw [← sub_div, toIocMod_sub_self]
  simp only [zsmul_eq_mul, Int.cast_neg]
  field_simp

theorem phase_exp_normalized (x : ℝ) :
    phase (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)) = Int.fract x := by
  rw [phase_exp]
  congr 1
  field_simp

/-- Tangential approach to the phase cut, from the prescribed side. -/
def cutApproach (ε : ℝ) : ℂ := (1 - ε ^ 2 : ℝ) + ε * Complex.I

theorem norm_cutApproach_lt_one {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ‖cutApproach ε‖ < 1 := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)).mp
  rw [← Complex.normSq_eq_norm_sq]
  have hsq : ε ^ 2 < 1 := by nlinarith [mul_pos hε (sub_pos.mpr hε')]
  simp only [cutApproach, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, one_pow]
  nlinarith [mul_pos (sq_pos_of_pos hε) (sub_pos.mpr hsq)]

/-- The polar angle encoded by a doubled exponential. -/
theorem exp_two_arg (x : ℂ) (hx : x ≠ 0) :
    Complex.exp ((2 * x.arg : ℝ) * Complex.I) = x / star x := by
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have he : Complex.exp ((x.arg : ℂ) * Complex.I) = x / ‖x‖ := by
    exact (eq_div_iff hn).mpr (by simpa [mul_comm] using Complex.norm_mul_exp_arg_mul_I x)
  rw [show ((2 * x.arg : ℝ) : ℂ) * Complex.I =
    (x.arg : ℂ) * Complex.I + (x.arg : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, he]
  have hsq : (‖x‖ : ℂ) ^ 2 = star x * x := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_eq_conj_mul_self
  have hstar : star x ≠ 0 := star_ne_zero.mpr hx
  rw [div_mul_div_comm, ← pow_two, ← pow_two, hsq]
  field_simp

/-- Exact scalar phase away from its cut, expressed by the logarithm in the disk. -/
theorem phase_eq_arg_one_sub {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    phase z = 1 / 2 + (1 - z).arg / Real.pi := by
  have hx : 1 - z ≠ 0 := sub_ne_zero.mpr hz'.symm
  have hc : z * star z = 1 := by
    simpa [Complex.normSq_eq_norm_sq, hz] using (Complex.mul_conj z)
  have hre : 0 < (1 - z).re := by
    have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, hz, pow_two] using Complex.normSq_eq_norm_sq z
    have hl : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
    have hne : z.re ≠ 1 := by
      intro h
      have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
      exact hz' (Complex.ext h hi)
    simpa using sub_pos.mpr (lt_of_le_of_ne hl hne)
  let f : ℝ := 1 / 2 + (1 - z).arg / Real.pi
  have hlow : -(Real.pi / 2) < (1-z).arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)
  have hupp : (1-z).arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hf0 : 0 ≤ f := by
    have hh : -(1/2:ℝ) < (1-z).arg / Real.pi :=
      (lt_div_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp [f]
    linarith
  have hf1 : f < 1 := by
    have hh : (1-z).arg / Real.pi < (1/2:ℝ) :=
      (div_lt_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp [f]
    linarith
  have hq : (1 - z) / star (1 - z) = -z := by
    apply (div_eq_iff (star_ne_zero.mpr hx)).mpr
    simp only [star_sub, star_one]
    linear_combination -hc
  have he : Complex.exp ((2 * Real.pi * f : ℝ) * Complex.I) = z := by
    have ha : ((2 * Real.pi * f : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I + ((2 * (1-z).arg : ℝ) : ℂ) * Complex.I := by
      dsimp [f]
      push_cast
      field_simp
    rw [ha, Complex.exp_add, Complex.exp_pi_mul_I, exp_two_arg _ hx, hq]
    ring
  calc
    phase z = phase (Complex.exp ((2 * Real.pi * f : ℝ) * Complex.I)) :=
      congrArg phase he.symm
    _ = Int.fract f := phase_exp_normalized f
    _ = 1 / 2 + (1-z).arg / Real.pi := Int.fract_eq_self.mpr ⟨hf0, hf1⟩

/-- The regularization used in the trace inequality. -/
def smoothPhase (a z : ℂ) : ℝ := 1 / 2 + (1 - a * z).arg / Real.pi

theorem re_one_sub_mul_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 < (1 - a * z).re := by
  have h : (a*z).re < 1 := (Complex.re_le_norm _).trans_lt
    ((norm_mul_le a z).trans_lt <| by nlinarith [norm_nonneg a, norm_nonneg z])
  simpa using sub_pos.mpr h

theorem smoothPhase_mem_Icc {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    smoothPhase a z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr (re_one_sub_mul_pos ha hz).le
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hl' : -(1/2:ℝ) ≤ (1-a*z).arg / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith)
  have hu' : (1-a*z).arg / Real.pi ≤ (1/2:ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith)
  dsimp [smoothPhase]
  constructor <;> linarith

theorem re_one_sub_pos {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    0 < (1-z).re := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hz, pow_two] using Complex.normSq_eq_norm_sq z
  have hl : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
  have hne : z.re ≠ 1 := by
    intro h
    have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact hz' (Complex.ext h hi)
  simpa using sub_pos.mpr (lt_of_le_of_ne hl hne)

/-- The tangential limit agrees with the discontinuous phase, also at one. -/
theorem tendsto_smoothPhase_cut {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun ε : ℝ => smoothPhase (cutApproach ε) z)
      (𝓝[>] 0) (𝓝 (phase z)) := by
  have hc : Continuous cutApproach := by unfold cutApproach; fun_prop
  have hca : Tendsto cutApproach (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [cutApproach] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  by_cases hz' : z = 1
  · subst z
    have ha : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I)
        (𝓝[>] 0) (𝓝 (-Complex.I)) := by
      have hcont : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hs : -Complex.I ∈ Complex.slitPlane := by
      simp [Complex.mem_slitPlane_iff]
    have ht := (Complex.continuousAt_arg hs).tendsto.comp ha
    have he : (fun ε : ℝ => (1 - cutApproach ε).arg) =ᶠ[𝓝[>] 0]
        (fun ε => ((ε : ℂ) - Complex.I).arg) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [show 1 - cutApproach ε = (ε : ℂ) * ((ε : ℂ) - Complex.I) by
        unfold cutApproach; push_cast; ring]
      exact Complex.arg_real_mul _ hε
    have ht' := ht.congr' he.symm
    have heq : (1/2 : ℝ) + (-Complex.I).arg / Real.pi = 0 := by
      rw [Complex.arg_neg_I]
      field_simp
      norm_num
    have htt := (ht'.div_const Real.pi).const_add (1/2 : ℝ)
    rw [heq] at htt
    simpa [smoothPhase] using htt
  · have hs : 1-z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz hz'))
    have hm : Tendsto (fun ε : ℝ => cutApproach ε * z) (𝓝[>] 0) (𝓝 z) := by
      simpa using hca.mul_const z
    have ht := (Complex.continuousAt_arg hs).tendsto.comp
      (tendsto_const_nhds.sub hm)
    simpa [smoothPhase, phase_eq_arg_one_sub hz hz'] using
      (ht.div_const Real.pi).const_add (1/2 : ℝ)

/-- The Mercator sum realizes the same real phase regularization. -/
theorem smoothPhase_eq_series {a z : ℂ} (haz : ‖a * z‖ < 1) :
    smoothPhase a z = 1 / 2 -
      (∑' n : ℕ, (a * z) ^ (n+1) / (n+1)).im / Real.pi := by
  rw [(Complex.hasSum_taylorSeries_neg_log' haz).tsum_eq]
  simp [smoothPhase, sub_eq_add_neg, Complex.log_im, neg_div]

/-- A concrete sequence in the open disk approaching the required side of the cut. -/
def cutTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem cutTime_pos (n : ℕ) : 0 < cutTime n := by
  unfold cutTime
  positivity

theorem cutTime_lt_one (n : ℕ) : cutTime n < 1 := by
  unfold cutTime
  apply (div_lt_one (by positivity)).mpr
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem tendsto_cutTime : Tendsto cutTime atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Filter.Eventually.of_forall cutTime_pos⟩
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 2)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h

theorem norm_cutApproach_cutTime_lt_one (n : ℕ) : ‖cutApproach (cutTime n)‖ < 1 :=
  norm_cutApproach_lt_one (cutTime_pos n) (cutTime_lt_one n)

theorem tendsto_smoothPhase_cutTime {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun n : ℕ => smoothPhase (cutApproach (cutTime n)) z) atTop (𝓝 (phase z)) :=
  (tendsto_smoothPhase_cut hz).comp tendsto_cutTime

end KervaireScalarPhase

end

end OAI
