import OAI.Analysis.FourierLLogL.Fourier.Scale
/-! # Comparing the Fourier projections to the averaged Haar kernel -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

def centerWin : Set ℝ := Ico (-1/2) (1/2)

def ang (u t : ℝ) : ℝ := u * (2*π*t)

lemma phase_trig (u t : ℝ) :
    phase u t = ↑(Real.cos (ang u t)) + ↑(Real.sin (ang u t)) * Complex.I := by
  unfold phase ang
  rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma phase_sub (u x y : ℝ) :
    phase u (x-y) = phase u x * phase (-u) y := by
  rw [sub_eq_add_neg, phase_add]
  unfold phase
  simp

def dirichlet (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), phase k t

lemma dirichlet_cont (N : ℕ) : Continuous (dirichlet N) := by
  apply continuous_finsetSum
  exact fun _ _ => phase_cont _

lemma dirichlet_bound (N : ℕ) (t : ℝ) :
    ‖dirichlet N t‖ ≤ 2*(N:ℝ)+1 := by
  refine (norm_sum_le _ _).trans ?_
  simp only [phase_unimod, Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
  exact_mod_cast (by omega : ((N:ℤ)+1-(-(N:ℤ))).toNat ≤ 2*N+1)

lemma dirichlet_succ (N : ℕ) (t : ℝ) :
    dirichlet (N+1) t = dirichlet N t + ↑(2 * Real.cos (ang (N+1:ℕ) t)) := by
  unfold dirichlet
  let M : ℤ := N
  have heq : Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ) =
      insert (M+1) (insert (-M-1) (Finset.Icc (-M) M)) := by
    ext i
    simp only [Finset.mem_insert, Finset.mem_Icc]
    dsimp [M]; omega
  have h1 : M+1 ∉ insert (-M-1) (Finset.Icc (-M) M) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    dsimp [M]; omega
  have h2 : -M-1 ∉ Finset.Icc (-M) M := by
    simp only [Finset.mem_Icc]; omega
  rw [heq, Finset.sum_insert h1, Finset.sum_insert h2]
  have h3 : ang ((↑(-M-1) : ℝ)) t = -ang (N+1:ℕ) t := by unfold M ang; push_cast; ring
  have h4 : ((↑(M+1):ℝ)) = ((N+1:ℕ):ℝ) := by simp [M]
  rw [phase_trig, phase_trig, h3, h4, Real.sin_neg, Real.cos_neg, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  dsimp only [M]
  ring

lemma dirichlet_sin (N : ℕ) (t : ℝ) :
    dirichlet N t * ↑(Real.sin (π*t)) = ↑(Real.sin (ang N t + π*t)) := by
  induction N with
  | zero => simp [dirichlet, phase, ang]
  | succ n ih =>
    rw [dirichlet_succ, add_mul, ih, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    congr 1
    have H : ang n t + π*t = ang (n+1:ℕ) t - π*t := by
      unfold ang; push_cast; ring
    rw [H, Real.sin_sub, Real.sin_add]
    ring

lemma sin_posabs {q : ℝ} (hq : |q| ≤ π/2) :
    |q|/2 ≤ |Real.sin q| := by
  have H := Real.mul_abs_le_abs_sin hq
  apply le_trans _ H
  have hc : 1/2 ≤ 2 / (π:ℝ) := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
  nlinarith [abs_nonneg q]

lemma dirichlet_id (N : ℕ) {t : ℝ} (ht : t ∈ centerWin) (hn : t ≠ 0) :
    dirichlet N t = ↑(Real.cos (ang N t) +
      Real.sin (ang N t) * (Real.cos (π*t) / Real.sin (π*t))) := by
  have hh : |π*t| ≤ π/2 := by
    rcases ht with ⟨h1,h2⟩
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]
  have hsin : Real.sin (π*t) ≠ 0 := by
    have H1 := abs_pos.mpr (mul_ne_zero Real.pi_pos.ne' hn)
    have H2 := sin_posabs hh
    intro h
    rw [h,abs_zero] at H2
    linarith
  have H := dirichlet_sin N t
  apply mul_right_cancel₀ (by exact_mod_cast hsin : (↑(Real.sin (π*t)) : ℂ) ≠ 0)
  rw [H, ← Complex.ofReal_mul, Real.sin_add]; congr 1; field_simp; ring

lemma cot_error {q : ℝ} (hq : |q| ≤ π/2) (hn : q ≠ 0) :
    |Real.cos q / Real.sin q - 1/q| ≤ 4 := by
  have hk := sin_posabs hq
  have hp : 0 < |q| := abs_pos.mpr hn
  have hs' : 0 < |Real.sin q| := by linarith
  have hs : Real.sin q ≠ 0 := abs_pos.mp hs'
  have h2 : |q| ≤ 2 := by linarith [Real.pi_lt_four]
  have hcos : |Real.cos q - 1| ≤ |q|^2 / 2 := by
    rw [abs_le, sq_abs]
    constructor
    · linarith [@Real.one_sub_sq_div_two_le_cos q]
    · nlinarith [Real.cos_le_one q]
  have H : |q * Real.cos q - Real.sin q| ≤ |q|^3 := by
    rw [show q * Real.cos q - Real.sin q = q * (Real.cos q - 1) + (q-Real.sin q) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    calc
      _ ≤ |q| * (|q|^2/2) + |q|^3/6 := add_le_add
        (mul_le_mul_of_nonneg_left hcos hp.le) (Real.abs_sub_sin_le q)
      _ ≤ _ := by nlinarith [pow_pos hp 3]
  rw [show Real.cos q / Real.sin q - 1/q = (q*Real.cos q - Real.sin q)/(q*Real.sin q) by field_simp,
    abs_div, abs_mul]
  apply (div_le_iff₀ (mul_pos hp hs')).mpr
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg |q|)])

def κfactor := 1 / (π * constK)

lemma κfactor_bound : |κfactor| ≤ 4 := by
  unfold κfactor constK
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ (by positivity)]
  norm_num
  linarith [Real.two_le_pi]

/-- Dirichlet profile minus rescaled approximate Hilbert profile modulated by sine. -/
def diffK (δ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  centerWin.indicator (dirichlet N) t -
    ↑(κfactor * kernel δ t * Real.sin (ang N t))

theorem diffK_major {t δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1)
    (ht : t ∈ window) (N : ℕ) :
    ‖diffK δ N t‖ ≤ if |t| < δ then 70 * ((N:ℝ) + 1) else 20 := by
  have hs : |Real.sin (ang N t)| ≤ 1 := Real.abs_sin_le_one _
  have hcc := κfactor_bound
  have htw : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2.le⟩
  split_ifs with H
  · apply (norm_sub_le _ _).trans
    have h1 : ‖centerWin.indicator (dirichlet N) t‖ ≤ 2*(N:ℝ)+1 := by
      by_cases h : t ∈ centerWin
      · simpa [h] using dirichlet_bound N t
      · simp only [indicator_of_notMem h, norm_zero]; positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
    have h2 : |Real.sin (ang N t)| ≤ (N:ℝ)*(8*δ) := by
      apply Real.abs_sin_le_abs.trans
      simp only [ang, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      gcongr
      linarith [Real.pi_lt_four]
    calc
      _ ≤ 2*(N:ℝ)+1+(4*(2/δ))*((N:ℝ)*(8*δ)) :=
        add_le_add h1 (mul_le_mul (mul_le_mul hcc (kernel_small hd hd' t)
          (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _) (by positivity))
      _ ≤ _ := by field_simp; nlinarith
  · have htpos : δ ≤ |t| := le_of_not_gt H
    have hn : t ≠ 0 := abs_pos.mp (hd.trans_le htpos)
    have hk := kernel_middle hd htpos htw
    by_cases hc : t ∈ centerWin
    · have hθ : |π*t| ≤ π/2 := by
        rcases hc with ⟨h1,h2⟩
        rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]
      have hA : |Real.cos (π*t) / Real.sin (π*t) - κfactor * kernel δ t| ≤ 4 + 4 * 2 := by
        rw [show Real.cos (π*t) / Real.sin (π*t) - κfactor * kernel δ t =
          (Real.cos (π*t)/Real.sin (π*t)-1/(π*t)) + (-κfactor)*(kernel δ t-constK/t) by
          unfold κfactor constK
          have := Real.pi_pos
          field_simp
          all_goals ring]
        apply (abs_add_le _ _).trans
        rw [abs_mul, abs_neg]
        exact add_le_add (cot_error hθ (mul_ne_zero Real.pi_pos.ne' hn))
          (mul_le_mul hcc hk (abs_nonneg _) (by norm_num))
      unfold diffK
      rw [indicator_of_mem hc, dirichlet_id _ hc hn, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      rw [show Real.cos (ang N t) + Real.sin (ang N t) * (Real.cos (π*t) / Real.sin (π*t)) -
          κfactor*kernel δ t*Real.sin (ang N t) = Real.cos (ang N t) +
          Real.sin (ang N t)*(Real.cos (π*t)/Real.sin (π*t)-κfactor*kernel δ t) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_mul]
      refine (add_le_add (Real.abs_cos_le_one _) (mul_le_mul hs hA (abs_nonneg _) zero_le_one)).trans ?_
      norm_num
    · have htl : 1/2 ≤ |t| := by unfold centerWin at hc; grind
      unfold diffK
      rw [indicator_of_notMem hc, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
      have he : |constK/t| ≤ 1 := by
        rw [abs_div, div_le_one (abs_pos.mpr hn)]
        unfold constK
        norm_num
        linarith
      have hQ : |kernel δ t| ≤ 3 := by rw [abs_le] at *; grind
      exact (mul_le_mul (mul_le_mul hcc hQ (abs_nonneg _) (by norm_num)) hs
        (abs_nonneg _) (by norm_num)).trans (by norm_num)

end
end FourierLLogL.Period

end OAI
