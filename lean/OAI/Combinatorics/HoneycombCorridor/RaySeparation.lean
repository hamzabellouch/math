import Mathlib
import OAI.Combinatorics.HoneycombCorridor.VisitRecursion

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def positiveWordMass (S : Finset (List Bool)) : ℝ :=
  ∑ w ∈ S, criticalActivity ^ w.length
noncomputable def phasedWordMass (S : Finset (List Bool)) : ℂ :=
  ∑ w ∈ S, wordWeight w
noncomputable def phase (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

@[simp] theorem phase_norm (a : ℝ) : ‖phase a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I a

theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  simp only [phase,Complex.ofReal_add,add_mul,Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem wordWeight_norm (w : List Bool) :
    ‖wordWeight w‖ = criticalActivity ^ w.length := by
  rw [wordWeight_turnUnits,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos criticalActivity_pos]

theorem positiveWordMass_nonneg (S : Finset (List Bool)) : 0 ≤ positiveWordMass S :=
  Finset.sum_nonneg fun _ _ => pow_nonneg criticalActivity_pos.le _

theorem phasedWordMass_norm_le (S : Finset (List Bool)) :
    ‖phasedWordMass S‖ ≤ positiveWordMass S := by
  simpa only [phasedWordMass,positiveWordMass,wordWeight_norm] using norm_sum_le S wordWeight

theorem positiveWordMass_mono {S T : Finset (List Bool)} (h : S ⊆ T) :
    positiveWordMass S ≤ positiveWordMass T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => pow_nonneg criticalActivity_pos.le _)

noncomputable def rayContraction : ℝ :=
  (1 + Real.cos (3*Real.pi/8) * Real.sin (Real.pi/8))⁻¹

theorem rayContraction_range : 0 < rayContraction ∧ rayContraction < 1 := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi/8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hd := mul_pos hc hs
  constructor
  · exact inv_pos.mpr (by linarith)
  · apply (inv_lt_one₀ (by linarith : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))).mpr
    linarith

theorem separated_rays_contract (S T : Finset (List Bool)) (hTS : T ⊆ S)
    (hlower : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ (phasedWordMass T).re)
    (a b : ℝ) (hb : 0 ≤ b)
    (hS : phasedWordMass S = (a : ℂ) * phase (-Real.pi/8))
    (hT : phasedWordMass T = (b : ℂ) * phase (-Real.pi/4)) :
    positiveWordMass T ≤ rayContraction * positiveWordMass S := by
  have halpha : Real.pi/8 + -Real.pi/4 = -Real.pi/8 := by ring
  have hzero : Real.pi/8 + -Real.pi/8 = 0 := by ring
  have hrotate : phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T) =
      (a : ℂ) - (b : ℂ) * phase (-Real.pi/8) := by
    rw [hS,hT,mul_sub]
    have h1 := phase_add (Real.pi/8) (-Real.pi/8)
    have h2 := phase_add (Real.pi/8) (-Real.pi/4)
    rw [hzero,phase_zero] at h1
    rw [halpha] at h2
    calc
      _ = (a : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/8)) -
          (b : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/4)) := by ring
      _ = _ := by rw [← h1,← h2,mul_one]
  have him : (phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im =
      b * Real.sin (Real.pi/8) := by
    rw [hrotate]
    have hp : (phase (-Real.pi/8)).im = -Real.sin (Real.pi/8) := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_im,neg_div,Real.sin_neg]
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,hp,zero_sub,zero_mul,add_zero,mul_neg,neg_neg]
  have hnorm : b * Real.sin (Real.pi/8) ≤ ‖phasedWordMass S - phasedWordMass T‖ := by
    calc
      _ ≤ |(phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im| := by
        rw [him]; exact le_abs_self _
      _ ≤ ‖phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)‖ :=
        Complex.abs_im_le_norm _
      _ = _ := by rw [norm_mul,phase_norm,one_mul]
  have hbnd : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ b := by
    calc
      _ ≤ (phasedWordMass T).re := hlower
      _ ≤ ‖phasedWordMass T‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = b := by rw [hT,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  have hmass : positiveWordMass (S \ T) + positiveWordMass T = positiveWordMass S :=
    Finset.sum_sdiff hTS
  have hdiff : phasedWordMass S - phasedWordMass T = phasedWordMass (S \ T) :=
    (Finset.sum_sdiff_eq_sub hTS).symm
  rw [hdiff] at hnorm
  have hnorm' := phasedWordMass_norm_le (S \ T)
  have hs : 0 ≤ Real.sin (Real.pi/8) := (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).le
  have hprod := mul_le_mul_of_nonneg_right hbnd hs
  have hfinal : (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))*positiveWordMass T ≤
      positiveWordMass S := by nlinarith
  change _ ≤ (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))⁻¹ * _
  have hd : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8) := by
    have hc : 0 ≤ Real.cos (3*Real.pi/8) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    nlinarith [mul_nonneg hc hs]
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hfinal)

end PolynomialVacuumBridge.Corridor

end

end OAI
