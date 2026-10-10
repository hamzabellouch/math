import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRegularMellin
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformWeights

namespace OAI

/-! Uniform rapid height decay of the actual zero-mode Voronoi pole. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma norm_metaplecticCompletedResidue_le {r : Eisenstein} (hr : primary r) :
    ‖metaplecticCompletedResidue r‖ ≤ |metaplecticA0| *norm r^(-1/6:ℝ) := by
  have hn := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hphi := metaplecticTotient_le_norm hr
  have hphi0 : 0 ≤ metaplecticTotient r := by unfold metaplecticTotient; positivity
  rw [metaplecticCompletedResidue,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_nonneg hphi0,abs_of_pos (Real.rpow_pos_of_pos hn _)]
  calc
    _ ≤ |metaplecticA0| *norm r*norm r^(-7/6:ℝ) := by gcongr
    _ = _ := by
      have hs : norm r*norm r^(-7/6:ℝ) = norm r^(-1/6:ℝ) := by
        calc
          _ = norm r^(1:ℝ)*norm r^(-7/6:ℝ) := by rw [Real.rpow_one]
          _ = norm r^((1:ℝ)+(-7/6)) := (Real.rpow_add hn _ _).symm
          _ = _ := by norm_num
      rw [mul_assoc,hs]

theorem UniformLogWeights.metaplectic_completed_pole_bound
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, primary r → ∀ X : ℝ, 0 < X →
      ∀ T : ℝ, 0 < T → ∀ t : ℝ, T ≤ |t| →
      ‖mellinPhase t X*metaplecticMain r 0 (fun x => W i x*mellinPhase t x) X‖ ≤
        C*X^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨K,hK,hdecay⟩ := h.mellin_decay (5/6) D
  refine ⟨|metaplecticA0| *K,by positivity,?_⟩
  intro i r hr X hX T hT t ht
  have hm : ‖mellin (fun x => W i x*mellinPhase t x) (5/6)‖ ≤ K/T^D := by
    rw [mellin_mul_phase]
    have hbound : ‖mellin (W i) ((5/6:ℝ)+(t:ℂ)*Complex.I)‖ ≤ K/(1+|t|)^D := by
      apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^D)).mpr
      simpa only [mul_comm] using hdecay i (5/6) (by norm_num) t
    have hb : ‖mellin (W i) (5/6+(t:ℂ)*Complex.I)‖ ≤ K/(1+|t|)^D := by
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using hbound
    apply hb.trans
    exact div_le_div_of_nonneg_left hK.le (pow_pos hT D)
      (pow_le_pow_left₀ hT.le (by linarith) D)
  rw [norm_mul,mellinPhase_norm,one_mul,metaplecticMain_zero_mode,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hX.le _)]
  calc
    _ ≤ (|metaplecticA0| *norm r^(-1/6:ℝ))*(K/T^D)*X^(5/6:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (norm_metaplecticCompletedResidue_le hr) hm (_root_.norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg r) _))) (by positivity)
    _ = _ := by ring

lemma interval_mean_norm_le_centered (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    {T E : ℝ} (hT : 0 < T) (hE : ∀ t ∈ Icc T (2*T), ‖g t‖ ≤ E) :
    (∫ t in T..2*T, ‖f t‖)/T ≤ (∫ t in T..2*T, ‖f t-g t‖)/T+E := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : T ≤ 2*T)
    (hf.norm.intervalIntegrable _ _)
    (((hf.sub hg).norm.add continuous_const).intervalIntegrable _ _)
    (show ∀ t ∈ Icc T (2*T), ‖f t‖ ≤ ‖f t-g t‖+E from fun t ht => by
      calc
        _ = ‖(f t-g t)+g t‖ := by rw [sub_add_cancel]
        _ ≤ ‖f t-g t‖+‖g t‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl (hE t ht))
  apply (div_le_iff₀ hT).mpr
  apply hi.trans_eq
  change (∫ t in T..2*T, ‖f t-g t‖+E) = _
  have hc : IntervalIntegrable (fun t => ‖f t-g t‖) volume T (2*T) :=
    (hf.sub hg).norm.intervalIntegrable _ _
  have he : IntervalIntegrable (fun _ : ℝ => E) volume T (2*T) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc he,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
