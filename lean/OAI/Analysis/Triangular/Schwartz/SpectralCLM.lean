import OAI.Analysis.Triangular.Schwartz.TailSpectral

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev Spectrum := Set.Icc (-(5/6):ℝ) (5/6)

def coeffAbs (l : Fin 31) : ℝ := ‖fourierCoeff l‖
lemma fourierCoeff_norm (l : Fin 31) : ‖fourierCoeff l‖ = coeffAbs l := rfl
def pVariation : ℝ := ∑ l : Fin 31, coeffAbs l
def dVariation : ℝ := (∑ l : Fin 31, coeffAbs l * |frequency l|)*Real.pi
def cVariation : ℝ := (∑ l : Fin 31, coeffAbs l * (frequency l)^2)*Real.pi^2/2
lemma coeffAbs_nonneg (l : Fin 31) : 0 ≤ coeffAbs l := norm_nonneg _

 def extend (f : C(Spectrum,ℂ)) (t : ℝ) : ℂ := f (Set.projIcc (-(5/6)) (5/6) (by norm_num) t)
lemma continuous_extend (f : C(Spectrum,ℂ)) : Continuous (extend f) := by
  exact f.continuous.comp continuous_projIcc
lemma norm_extend_le (f : C(Spectrum,ℂ)) (t : ℝ) : ‖extend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

lemma frequency_mem (l : Fin 31) : frequency l ∈ Set.Icc (-(5/6):ℝ) (5/6) := by
  unfold frequency
  have hn : (l.val:ℝ) ≤ 30 := by exact_mod_cast (show l.val ≤ 30 by omega)
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) l.val]

def spectralC (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (-(Real.pi:ℂ)^2 * ∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

def spectralD (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (I*Real.pi * ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

def spectralP (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * f ⟨frequency l,frequency_mem l⟩

lemma norm_exp_phase (t : ℝ) (n : ℤ) : ‖exp (I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_exp_neg_phase (t : ℝ) (n : ℤ) : ‖exp (-I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_first_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, f r‖ ≤ M*|t| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => hM r) (a := 0) (b := t)

lemma norm_second_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, ((t:ℂ)-r)*f r‖ ≤ M*t^2/2 := by
  by_cases ht : 0 ≤ t
  · calc
      _ ≤ ∫ r in (0:ℝ)..t, (t-r)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hr.2)]
            exact mul_le_mul_of_nonneg_left (hM r) (sub_nonneg.mpr hr.2)
        · exact (show Continuous (fun r : ℝ => (t-r)*M) by fun_prop).intervalIntegrable 0 t
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun _ : ℝ => t) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _), integral_id]
        simp only [intervalIntegral.integral_const, sub_zero, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring
  · have ht' := le_of_not_ge ht
    rw [intervalIntegral.integral_symm, norm_neg]
    calc
      _ ≤ ∫ r in t..(0:ℝ), (r-t)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht'
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr hr.1.le)]
            calc
              _ ≤ (-(t-r))*M := mul_le_mul_of_nonneg_left (hM r) (by linarith [hr.1])
              _ = _ := by ring
        · exact (show Continuous (fun r : ℝ => (r-t)*M) by fun_prop).intervalIntegrable t 0
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => t)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id]
        simp only [intervalIntegral.integral_const, zero_sub, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring

lemma spectralP_bound (f : C(Spectrum,ℂ)) : ‖spectralP f‖ ≤ pVariation*‖f‖ := by
  calc
    _ ≤ ∑ l : Fin 31, coeffAbs l * ‖f‖ := by
      unfold spectralP
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      rw [norm_mul,fourierCoeff_norm]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (by rw [←fourierCoeff_norm]; positivity)
    _ = _ := by rw [←Finset.sum_mul]; rfl

lemma spectralD_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralD n f‖ ≤ dVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤ ‖f‖*|frequency l| := by
    apply norm_first_integral_le
    intro t
    rw [norm_mul,norm_exp_neg_phase,one_mul]
    exact norm_extend_le f t
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * |frequency l|) * (Real.pi*‖f‖) := by
      unfold spectralD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
      calc
        _ ≤ coeffAbs l * (Real.pi * (‖f‖*|frequency l|)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [dVariation]; ring

lemma spectralC_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralC n f‖ ≤ cVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤
      ‖f‖*(frequency l)^2/2 := by
    have hi := norm_second_integral_le (fun t => exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t) ‖f‖
      (fun t => by rw [norm_mul,norm_exp_neg_phase,one_mul]; exact norm_extend_le f t) (frequency l)
    simpa only [mul_assoc] using hi
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * (frequency l)^2) * (Real.pi^2/2*‖f‖) := by
      unfold spectralC
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      calc
        _ ≤ coeffAbs l * (Real.pi^2 * (‖f‖*(frequency l)^2/2)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [cVariation]; ring

def integralLinear (w : ℝ → ℂ) (hw : Continuous w) (t : ℝ) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ r in (0:ℝ)..t, w r * extend f r
  map_add' f g := by
    simp only [extend,ContinuousMap.add_apply,mul_add]
    apply intervalIntegral.integral_add
    · exact (hw.mul (continuous_extend f)).intervalIntegrable 0 t
    · exact (hw.mul (continuous_extend g)).intervalIntegrable 0 t
  map_smul' c f := by
    simp only [extend,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (w _) c]
    exact intervalIntegral.integral_const_mul _ _

def spectralCLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (-(Real.pi:ℂ)^2)) •
    integralLinear (fun t => ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

def spectralDLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (I*Real.pi)) •
    integralLinear (fun t => exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

lemma spectralCLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralCLinear n f = spectralC n f := by
  simp [spectralCLinear,spectralC,integralLinear,mul_assoc]
lemma spectralDLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralDLinear n f = spectralD n f := by
  simp [spectralDLinear,spectralD,integralLinear,mul_assoc]

def spectralCCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralCLinear n).mkContinuous cVariation (by
    intro f; rw [spectralCLinear_apply]; exact spectralC_bound n f)
def spectralDCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralDLinear n).mkContinuous dVariation (by
    intro f; rw [spectralDLinear_apply]; exact spectralD_bound n f)
def spectralPCLM : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  ∑ l : Fin 31, fourierCoeff l • ContinuousMap.evalCLM ℂ ⟨frequency l,frequency_mem l⟩

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs]; positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs]; positivity) _
lemma spectralPCLM_norm : ‖spectralPCLM‖ ≤ pVariation := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold pVariation coeffAbs; positivity)
  intro f
  rw [spectralPCLM_apply]
  exact spectralP_bound f

def phaseFunction (s : ℂ) : C(Spectrum,ℂ) :=
  ⟨fun t => exp (I*Real.pi*(t.val:ℂ)*s), by fun_prop⟩

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma interval_frequency_subset (l : Fin 31) : Set.uIcc 0 (frequency l) ⊆ Spectrum := by
  have h := Set.uIcc_subset_uIcc (show (0:ℝ) ∈ Set.uIcc (-(5/6)) (5/6) by norm_num)
    (show frequency l ∈ Set.uIcc (-(5/6)) (5/6) by simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using frequency_mem l)
  simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using h

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

def frequencyFunction : C(Spectrum,ℂ) := ⟨fun t => I*Real.pi*(t.val:ℂ), by fun_prop⟩

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
