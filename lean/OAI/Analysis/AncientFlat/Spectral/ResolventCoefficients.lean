import OAI.Analysis.AncientFlat.Kernel.FourierDecay

namespace OAI
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace PeriodicResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
lemma osc_periodic (n : ℤ) : Function.Periodic (osc n) 1 := by
  intro t
  calc
    osc n (t+1)=osc n t*osc n 1 := by
      simp only [osc, Complex.ofReal_add, mul_add, Complex.exp_add]
    _=osc n t := by rw [osc_one, mul_one]
lemma osc_smooth (n : ℤ) : ContDiff ℝ ∞ (osc n) := by
  have hreal : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul hreal).cexp
lemma freq_ne_zero {n : ℤ} (hn : n≠0) : freq n≠0 := by
  simp only [freq, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Complex.I_ne_zero,
    or_false, not_or]
  exact ⟨⟨by norm_num, Real.pi_ne_zero⟩, by exact_mod_cast hn⟩
lemma coeff_const (v : E) (n : ℤ) : coeff (fun _ => v) n=if n=0 then v else 0 := by
  split_ifs with hn
  · subst n
    simp [coeff, osc, freq]
  · have h := coeff_derivative (fun _ : ℝ => v) (fun _ => (0:E)) continuous_const
      continuous_const (fun _ => hasDerivAt_const _ _) rfl n
    have hz : (-freq n) • coeff (fun _ : ℝ => v) n=0 := by simpa [coeff] using h.symm
    exact (smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (freq_ne_zero hn))

lemma coeff_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : ℝ → E) (hf : Continuous f) (n : ℤ) :
    coeff (fun t => L (f t)) n=L (coeff f n) := by
  unfold coeff
  simp_rw [← L.map_smul]
  exact L.intervalIntegral_comp_comm (((osc_continuous n).smul hf).intervalIntegrable 0 1)
omit [CompleteSpace E] in
lemma coeff_sub (f g : ℝ → E) (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    coeff (fun t => f t-g t) n=coeff f n-coeff g n := by
  simp only [coeff, smul_sub]
  exact intervalIntegral.integral_sub (((osc_continuous n).smul hf).intervalIntegrable 0 1)
    (((osc_continuous n).smul hg).intervalIntegrable 0 1)
omit [CompleteSpace E] in
lemma coeff_smul (f : ℝ → E) (a : ℂ) (n : ℤ) :
    coeff (fun t => a • f t) n=a • coeff f n := by
  simp only [coeff, smul_comm (osc n _) a, intervalIntegral.integral_smul]
omit [CompleteSpace E] in
lemma coeff_shift (f : ℝ → E) (n : ℤ) :
    coeff (fun t => osc 1 t • f t) n=coeff f (n+1) := by
  simp only [coeff, smul_smul, osc_add]

def resolventLoop (P : E →L[ℂ] E) (q : ℝ) (t : ℝ) : E →L[ℂ] E :=
  resolvent P ((q:ℂ)*osc 1 t)
lemma loop_smooth (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) :
    ContDiff ℝ ∞ (resolventLoop P q) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hunit : IsUnit (algebraMap ℂ (E →L[ℂ] E) ((q:ℂ)*osc 1 t)-P) :=
    hc _ (by simp [osc_norm, Complex.norm_real, Real.norm_eq_abs, hq.le])
  have hi : ContDiffAt ℝ ∞ Ring.inverse
      (algebraMap ℂ (E →L[ℂ] E) ((q:ℂ)*osc 1 t)-P) := by
    simpa only [hunit.unit_spec] using contDiffAt_ringInverse ℝ (n := ∞) hunit.unit
  have hz : ContDiff ℝ ∞ (fun s => ((q:ℂ)*osc 1 s) • (1:E →L[ℂ] E)-P) :=
    (contDiff_const.mul (osc_smooth 1)).smul contDiff_const |>.sub contDiff_const
  change ContDiffAt ℝ ∞ (fun s => resolvent P ((q:ℂ)*osc 1 s)) t
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one, Function.comp_def]
    using hi.comp t hz.contDiffAt
omit [CompleteSpace E] in
lemma loop_periodic (P : E →L[ℂ] E) (q : ℝ) :
    Function.Periodic (resolventLoop P q) 1 := by
  intro t
  simp only [resolventLoop, osc_periodic 1 t]
omit [CompleteSpace E] in
lemma loop_identity (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) (t : ℝ) :
    (q:ℂ) • (osc 1 t • resolventLoop P q t)-P*resolventLoop P q t=1 := by
  have h := hc ((q:ℂ)*osc 1 t)
    (by simp [osc_norm, Complex.norm_real, Real.norm_eq_abs, hq.le])
  rw [resolventLoop, spectrum.resolvent_eq h]
  have hu := h.unit.mul_inv
  simp only [h.unit_spec, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hu
  simpa only [smul_smul] using hu

theorem green_summable (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) :
    Summable (fun n : ℤ => ‖coeff (resolventLoop P q) n‖) :=
  summable_coeff_norm _ ((loop_smooth P hq hc).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))) (loop_periodic P q)
lemma green_identity (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) (n : ℤ) :
    (q:ℂ) • coeff (resolventLoop P q) (n+1)-P*coeff (resolventLoop P q) n=
      if n=0 then 1 else 0 := by
  have hf := (loop_smooth P hq hc).continuous
  have hm := coeff_map (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P) (resolventLoop P q) hf n
  have he := congrArg (fun f : ℝ → (E →L[ℂ] E) => coeff f n)
    (funext (loop_identity P hq hc))
  change coeff (fun t => P*resolventLoop P q t) n=P*coeff (resolventLoop P q) n at hm
  rw [coeff_sub (fun t => (q:ℂ) • (osc 1 t • resolventLoop P q t))
    (fun t => P*resolventLoop P q t)
    (((osc_continuous 1).smul hf).const_smul (q:ℂ))
    (continuous_const.mul hf), coeff_smul, coeff_shift, hm, coeff_const] at he
  exact he
end PeriodicResolvent

end

end OAI
