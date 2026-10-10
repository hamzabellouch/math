import Mathlib
import OAI.Probability.SKGap.Brownian.ContinuousPosteriorMass

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k)) (f : Spin n→ℝ)
    (h : History n k) : ℝ :=
  by classical exact if h∈A then var (posterior p t h) f else avg (posterior p t h) (fun x => (f x)^2)

lemma envelope_nonneg (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : 0≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · exact var_nonneg _ _
  · exact avg_nonneg _ _ (fun _ => sq_nonneg _)

lemma var_le_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : var (posterior p t h) f≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · rfl
  · exact var_le_square _ _

lemma envelope_le_square (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) :
    envelope p t A f h≤avg (posterior p t h) (fun x => (f x)^2) := by
  unfold envelope
  split_ifs
  · exact var_le_square _ _
  · rfl

lemma measurable_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) : Measurable (envelope p t A f) :=
  Measurable.ite hA (continuous_posterior_var p t k f).measurable
    (continuous_posterior_avg p t k _).measurable

lemma integrable_envelope_weight (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) :
    Integrable (fun h => density p t h*envelope p t A f h) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => (f x)^2) k).mono'
    (((continuous_density p t k).measurable.mul (measurable_envelope p t A hA f)).aestronglyMeasurable)
  filter_upwards [] with h
  change |density p t h*envelope p t A f h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (envelope_nonneg p t A f h))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le

def envelopeIntegral (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k)) (f : Spin n→ℝ) : ℝ :=
  ∫h,density p t h*envelope p t A f h ∂reference n k

lemma variance_le_envelope_zero (p : Prior n) (t : ℝ) (A : Set (History n 0)) (f : Spin n→ℝ) :
    var p f≤envelopeIntegral p t A f := by
  unfold envelopeIntegral reference
  rw [integral_dirac,density_zero,one_mul]
  have hh:=var_le_envelope p t A f ()
  rw [posterior_zero] at hh
  exact hh

lemma integrable_envelope_section (p : Prior n) (t : ℝ) {k : ℕ} (G : Set (History n (k+1)))
    (hG : MeasurableSet G) (f : Spin n→ℝ) (h : History n k) :
    Integrable (fun z => GaussianStep.density (posterior p t h) t z *
      envelope p t G f (h,z)) (GaussianStep.reference n) := by
  have hm : Measurable (fun z => envelope p t G f (h,z)) :=
    (measurable_envelope p t G hG f).comp (measurable_const.prodMk measurable_id)
  have hn : Integrable (fun z => GaussianStep.density (posterior p t h) t z*
      avg (posterior p t (k := k+1) (h,z)) (fun x => (f x)^2)) (GaussianStep.reference n) := by
    simp_rw [posterior_succ]
    exact GaussianStep.integrable_posterior_avg_weight _ t _
  apply hn.mono' (((GaussianStep.continuous_density (posterior p t h) t).measurable.mul hm).aestronglyMeasurable)
  filter_upwards [] with z
  change |GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)|≤_
  rw [abs_of_nonneg (mul_nonneg (GaussianStep.density_pos _ _ _).le (envelope_nonneg _ _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t G f (h,z)) (GaussianStep.density_pos _ _ _).le

lemma envelope_step_point (p : Prior n) (t : ℝ) {k : ℕ}
    (A : Set (History n k)) (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (h : History n k) :
    (1-D*t)*envelope p t A f h-D*t*energy (posterior p t h) f-
        16*(n:ℝ)^2*t^2*avg (posterior p t h) (fun x => (f x)^2) ≤
      ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
        ∂GaussianStep.reference n := by
  by_cases hh : h∈A
  · have hv : (∫z,GaussianStep.density (posterior p t h) t z*
        var (GaussianStep.posterior (posterior p t h) t z) f ∂GaussianStep.reference n) ≤
        ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
          ∂GaussianStep.reference n := by
      apply integral_mono (GaussianStep.integrable_posterior_variance_weight _ t f)
        (integrable_envelope_section p t G hG f h)
      intro z
      have he:=var_le_envelope p t G f (h,z)
      rw [posterior_succ] at he
      exact mul_le_mul_of_nonneg_left he (GaussianStep.density_pos _ _ _).le
    have hs:=GaussianStep.variance_step_bound (posterior p t h) ht htn f
    have hc:=mul_le_mul_of_nonneg_left (hgood h hh) ht
    have hn:=mul_le_mul_of_nonneg_left (var_le_square (posterior p t h) f)
      (show 0≤16*(n:ℝ)^2*t^2 by positivity)
    rw [envelope,ite_eq_left hh]
    nlinarith
  · have he (z : Fin n→ℝ) : envelope p t G f (h,z)=
        avg (GaussianStep.posterior (posterior p t h) t z) (fun x => (f x)^2) := by
      rw [envelope,ite_eq_right (fun hmem => hh (hprefix (h,z) hmem)),posterior_succ]
    simp_rw [he]
    rw [GaussianStep.integral_posterior_avg_weight _ ht,envelope,ite_eq_right hh]
    have hN : 0≤avg (posterior p t h) (fun x => (f x)^2) := avg_nonneg _ _ (fun _ => sq_nonneg _)
    have hE:=energy_nonneg (posterior p t h) f
    have hdt : 0≤D*t := mul_nonneg hD ht
    have herr : 0≤16*(n:ℝ)^2*t^2 := by positivity
    nlinarith [mul_nonneg hdt hN,mul_nonneg hdt hE,mul_nonneg herr hN]

theorem envelope_step_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} {k : ℕ}
    (A : Set (History n k)) (hA : MeasurableSet A)
    (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    (1-D*t)*envelopeIntegral p t A f-D*t*energy p f-
        16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) ≤ envelopeIntegral p t G f := by
  have hi:=integrable_envelope_weight p t G hG f
  change Integrable (fun hz : History n k × (Fin n→ℝ) => density p t (k := k+1) hz*envelope p t G f hz)
    ((reference n k).prod (GaussianStep.reference n)) at hi
  have hiR:=hi.integral_prod_left
  have he : (∫h:History n k,∫z,density p t (k := k+1) (h,z)*envelope p t G f (h,z)
      ∂GaussianStep.reference n ∂reference n k)=envelopeIntegral p t G f :=
    (integral_prod _ hi).symm
  have hi1:=(integrable_envelope_weight p t A hA f).const_mul (1-D*t)
  have hi2:=(integrable_posterior_energy_weight p hp t k f).const_mul (D*t)
  have hi3:=(integrable_posterior_avg_weight p t (fun x => (f x)^2) k).const_mul (16*(n:ℝ)^2*t^2)
  have hi12 : Integrable (fun h => (1-D*t)*(density p t h*envelope p t A f h)-
      D*t*(density p t h*energy (posterior p t h) f)) (reference n k) := hi1.sub hi2
  have hh:=integral_mono (hi12.sub hi3) hiR (fun h => ?_)
  swap
  · simp only [Pi.sub_apply]
    simp_rw [density_succ,mul_assoc]
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (envelope_step_point p t A G hG hprefix f ht htn D hD hgood h)
      (density_pos p t h).le using 1; ring
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi12 hi3,integral_sub hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_posterior_avg_weight p ht,he] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) (mul_nonneg hD ht)
  change (1-D*t)*envelopeIntegral p t A f-D*t*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)-
    16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2)≤envelopeIntegral p t G f at hh
  linarith

theorem envelope_terminal_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) {k : ℕ}
    (A E : Set (History n k)) (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hprefix : Aᶜ⊆E) (L : ℝ) (hL : 0≤L)
    (hterminal : ∀h:History n k,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    envelopeIntegral p t A f≤ L*energy p f+
      avg p (fun x => (f x)^2)*eventProbability (squarePrior p f hf) t E := by
  let N:=avg p (fun x => (f x)^2)
  have hi1:=(integrable_posterior_energy_weight p hp t k f).const_mul L
  have hi2:=((integrable_density (squarePrior p f hf) t k).indicator hE).const_mul N
  have hh:=integral_mono (integrable_envelope_weight p t A hA f) (hi1.add hi2) (fun h => ?_)
  swap
  · simp only [Pi.add_apply]
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,squarePrior_density]
      have henv:=mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le
      have hden : N*(density p t h*avg (posterior p t h) (fun x => (f x)^2)/N)=
          density p t h*avg (posterior p t h) (fun x => (f x)^2) := mul_div_cancel₀ _ hf.ne'
      change _≤L*(density p t h*energy (posterior p t h) f)+N*(_/N)
      rw [hden]
      exact henv.trans (le_add_of_nonneg_left (mul_nonneg hL
        (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))))
    · have ha : h∈A := by by_contra hn; exact he (hprefix hn)
      simp only [Set.indicator_of_notMem he,mul_zero,add_zero,envelope,ite_eq_left ha]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hterminal h he) (density_pos p t h).le
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul,integral_indicator hE] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) hL
  change envelopeIntegral p t A f≤L*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)+
    N*eventProbability (squarePrior p f hf) t E at hh
  dsimp [N] at hh
  linarith

end
end SKGap.GaussianHistory

end OAI
