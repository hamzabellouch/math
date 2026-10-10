import Mathlib
import OAI.Probability.SKRatio.Entropy.GaussianChannel
import OAI.Probability.SKRatio.Entropy.FiniteEntropy

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation

abbrev History (d : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => History d k × (Fin d → ℝ)

namespace History
variable {α : Type*} {d : ℕ}

@[reducible] instance historyMeasurable (d : ℕ) : (k : ℕ) → MeasurableSpace (History d k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    change MeasurableSpace (History d k × (Fin d → ℝ))
    letI := historyMeasurable d k
    infer_instance

@[reducible] instance historyTopology (d : ℕ) : (k : ℕ) → TopologicalSpace (History d k)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | k+1 => by
    change TopologicalSpace (History d k × (Fin d → ℝ))
    letI := historyTopology d k
    infer_instance

instance historySecondCountable (d : ℕ) : (k : ℕ) → SecondCountableTopology (History d k)
  | 0 => inferInstanceAs (SecondCountableTopology Unit)
  | k+1 => by
    change SecondCountableTopology (History d k × (Fin d → ℝ))
    let := historySecondCountable d k
    infer_instance

instance historyBorel (d : ℕ) : (k : ℕ) → BorelSpace (History d k)
  | 0 => inferInstanceAs (BorelSpace Unit)
  | k+1 => by
    change BorelSpace (History d k × (Fin d → ℝ))
    let := historyBorel d k
    infer_instance

def reference (d : ℕ) : (k : ℕ) → Measure (History d k)
  | 0 => Measure.dirac ()
  | k+1 => (reference d k).prod (Channel.reference d)

instance reference_probability (d : ℕ) : (k : ℕ) → IsProbabilityMeasure (reference d k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | k+1 => by
    change IsProbabilityMeasure ((reference d k).prod (Channel.reference d))
    let := reference_probability d k
    infer_instance

variable (v : α → Fin d → ℝ)

def likelihood (t : ℝ) (x : α) : {k : ℕ} → History d k → ℝ
  | 0, _ => 1
  | _+1, h => likelihood t x h.1 * Channel.likelihood v t x h.2

lemma likelihood_pos (t : ℝ) (x : α) : ∀ {k : ℕ} (h : History d k),
    0 < likelihood v t x h
  | 0, _ => zero_lt_one
  | _+1, h => mul_pos (likelihood_pos t x h.1) (Channel.likelihood_pos v t x h.2)

lemma continuous_likelihood (t : ℝ) (x : α) : ∀ k,
    Continuous (likelihood v t x (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_likelihood t x k).comp continuous_fst |>.mul
      ((Channel.continuous_likelihood v t x).comp continuous_snd)

lemma integrable_likelihood (t : ℝ) (x : α) : ∀ k,
    Integrable (likelihood v t x (k := k)) (reference d k)
  | 0 => by
    change Integrable (fun _ : Unit => (1:ℝ)) (Measure.dirac ())
    exact integrable_const 1
  | k+1 => (integrable_likelihood t x k).mul_prod (Channel.integrable_likelihood v t x)

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : α) : ∀ k,
    (∫ h : History d k, likelihood v t x h ∂reference d k) = 1
  | 0 => by
    change (∫ _ : Unit, (1:ℝ) ∂Measure.dirac ()) = 1
    rw [integral_dirac]
  | k+1 => by
    change (∫ h, likelihood v t x h.1 * Channel.likelihood v t x h.2
      ∂(reference d k).prod (Channel.reference d)) = 1
    rw [integral_prod_mul, integral_likelihood ht x k, Channel.integral_likelihood v ht, mul_one]

variable [Fintype α]

def density (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) : ℝ :=
  ∑ x, p x*likelihood v t x h

lemma density_pos (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) :
    0 < density v p t h := by
  have he : ∃ x, 0 < p x := by
    by_contra hn
    push Not at hn
    have hz : ∑ x, p x = 0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hn x) (p.nonneg x))
    linarith [p.sum_one]
  obtain ⟨x,hx⟩ := he
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (likelihood_pos v t y h).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (likelihood_pos v t x h)⟩

lemma continuous_density (p : Prior α) (t : ℝ) (k : ℕ) : Continuous (density v p t (k := k)) :=
  continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x k).const_mul (p x))

lemma integrable_density (p : Prior α) (t : ℝ) (k : ℕ) :
    Integrable (density v p t (k := k)) (reference d k) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x k).const_mul (p x))

lemma integral_density (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (∫ h : History d k, density v p t h ∂reference d k) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood v t x k).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood v ht, mul_one]
  exact p.sum_one

def posterior (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) : Prior α where
  mass x := p x*likelihood v t x h/density v p t h
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos v t x h).le) (density_pos v p t h).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (density_pos v p t h).ne'

lemma density_zero (p : Prior α) (t : ℝ) (h : History d 0) : density v p t h=1 := by
  simp only [density, likelihood, mul_one, p.sum_one]

lemma posterior_zero (p : Prior α) (t : ℝ) (h : History d 0) : posterior v p t h=p := by
  apply Prior.ext
  funext x
  change p x*1/density v p t h=p x
  rw [density_zero v, mul_one, div_one]

lemma density_succ (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (z : Fin d → ℝ) :
    density v p t (k := k+1) (h,z) = density v p t h*Channel.density v (posterior v p t h) t z := by
  change (∑ x, p x*(likelihood v t x h*Channel.likelihood v t x z)) =
    density v p t h*(∑ x, (p x*likelihood v t x h/density v p t h)*Channel.likelihood v t x z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos v p t h).ne']

lemma posterior_succ (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (z : Fin d → ℝ) :
    posterior v p t (k := k+1) (h,z) = Channel.posterior v (posterior v p t h) t z := by
  apply Prior.ext
  funext x
  change p x*(likelihood v t x h*Channel.likelihood v t x z)/density v p t (k := k+1) (h,z) =
    (p x*likelihood v t x h/density v p t h)*Channel.likelihood v t x z /
      Channel.density v (posterior v p t h) t z
  rw [density_succ v]
  field_simp [(density_pos v p t h).ne', (Channel.density_pos v (posterior v p t h) t z).ne']

lemma posterior_avg_weight (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) (f : α → ℝ) :
    density v p t h*avg (posterior v p t h) f=∑ x, p x*likelihood v t x h*f x := by
  simp only [avg,FiniteLaw.mean, posterior, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos v p t h).ne']

lemma integrable_posterior_avg_weight (p : Prior α) (t : ℝ) (f : α → ℝ) (k : ℕ) :
    Integrable (fun h : History d k => density v p t h*avg (posterior v p t h) f) (reference d k) := by
  simp_rw [posterior_avg_weight v]
  exact integrable_finsetSum _ (fun x _ => ((integrable_likelihood v t x k).const_mul (p x)).mul_const (f x))

lemma integral_posterior_avg_weight (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (f : α → ℝ) (k : ℕ) :
    (∫ h : History d k, density v p t h*avg (posterior v p t h) f ∂reference d k)=avg p f := by
  simp_rw [posterior_avg_weight v]
  rw [integral_finsetSum _ (fun x _ => ((integrable_likelihood v t x k).const_mul (p x)).mul_const (f x))]
  simp_rw [integral_mul_const, integral_const_mul, integral_likelihood v ht, mul_one]
  rfl

lemma posterior_mass_pos (p : Prior α) (hp : ∀ x,0 < p x) (t : ℝ)
    {k : ℕ} (h : History d k) (x : α) : 0 < posterior v p t h x :=
  div_pos (mul_pos (hp x) (likelihood_pos v t x h)) (density_pos v p t h)

lemma continuous_posterior_mass (p : Prior α) (t : ℝ) (k : ℕ) (x : α) :
    Continuous (fun h : History d k => posterior v p t h x) :=
  ((continuous_likelihood v t x k).const_mul (p x)).div (continuous_density v p t k)
    (fun h => (density_pos v p t h).ne')

lemma continuous_posterior_entropy (p : Prior α) (f : α → ℝ) (t : ℝ) (k : ℕ) :
    Continuous (fun h : History d k => ent (posterior v p t h) f) :=
  (continuous_entropy_masses f).comp (continuous_pi (continuous_posterior_mass v p t k))

lemma integrable_posterior_entropy_weight (p : Prior α) (f : α → ℝ) (hf : ∀ x,0<f x)
    (t : ℝ) (k : ℕ) :
    Integrable (fun h : History d k => density v p t h*ent (posterior v p t h) f) (reference d k) := by
  apply ((integrable_density v p t k).mul_const (∑ x,logRemainder (f x) 1)).mono'
    ((continuous_density v p t k).mul (continuous_posterior_entropy v p f t k)).aestronglyMeasurable
  filter_upwards [] with h
  change |density v p t h*ent (posterior v p t h) f| ≤ _
  rw [abs_of_nonneg (mul_nonneg (density_pos v p t h).le (ent_nonneg _ hf))]
  exact mul_le_mul_of_nonneg_left (ent_bound _ f hf) (density_pos v p t h).le

def remainingEntropy (p : Prior α) (f : α → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∫ h : History d k, density v p t h*ent (posterior v p t h) f ∂reference d k

lemma remainingEntropy_zero (p : Prior α) (f : α → ℝ) (t : ℝ) :
    remainingEntropy v p f t 0=ent p f := by
  unfold remainingEntropy
  simp only [density_zero,posterior_zero,one_mul]
  change (∫ _ : Unit, ent p f ∂Measure.dirac ()) = ent p f
  rw [integral_dirac]

lemma remainingEntropy_succ (p : Prior α) (f : α → ℝ) (hf : ∀ x,0<f x)
    (t : ℝ) (k : ℕ) : remainingEntropy v p f t (k+1) =
      ∫ h : History d k, density v p t h*
        (∫ z, Channel.density v (posterior v p t h) t z*
          ent (Channel.posterior v (posterior v p t h) t z) f ∂Channel.reference d) ∂reference d k := by
  unfold remainingEntropy
  rw [show reference d (k+1) = (reference d k).prod (Channel.reference d) from rfl,
    integral_prod _ (integrable_posterior_entropy_weight v p f hf t (k+1))]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [density_succ,posterior_succ,mul_assoc,integral_const_mul]

lemma entropy_recurrence (p : Prior α) (hp : ∀ x,0<p x) (f : α → ℝ) (hf : ∀ x,0<f x)
    {C K t : ℝ} (hC : 0<C) (ht : 0≤t) (hK : 0≤K)
    (hbound : ∀ q : Prior α, ∀ x y, |Channel.interaction v q x y| ≤ K)
    (hKt : K*t≤1) (k : ℕ)
    (hvar : ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p t h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2)) :
    (1-2*C*t)*remainingEntropy v p f t k-4*K^2*t^2*avg p f ≤
      remainingEntropy v p f t (k+1) := by
  have hi := (integrable_posterior_entropy_weight v p f hf t (k+1)).integral_prod_left
  simp_rw [density_succ,posterior_succ,mul_assoc,integral_const_mul] at hi
  have hl := ((integrable_posterior_entropy_weight v p f hf t k).const_mul (1-2*C*t)).sub
    ((integrable_posterior_avg_weight v p t f k).const_mul (4*K^2*t^2))
  have hh := integral_mono hl hi (fun h => by
    have hh := mul_le_mul_of_nonneg_left
      (Channel.entropy_retention v (posterior v p t h) f hf (posterior_mass_pos v p hp t h)
        hC ht hK (hbound _) hKt (hvar h)) (density_pos v p t h).le
    convert! hh using 1
    dsimp
    ring)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub ((integrable_posterior_entropy_weight v p f hf t k).const_mul (1-2*C*t))
      ((integrable_posterior_avg_weight v p t f k).const_mul (4*K^2*t^2)),
    integral_const_mul,integral_const_mul,integral_posterior_avg_weight v p ht] at hh
  rw [remainingEntropy_succ v p f hf t k]
  exact hh

lemma affine_lower (u : ℕ → ℝ) {r b : ℝ} (hr : 0≤r) (hr1 : r≤1) (hb : 0≤b)
    (N : ℕ) (hstep : ∀ k<N, r*u k-b≤u (k+1)) :
    r^N*u 0-(N:ℝ)*b≤u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self N)))) hr
    have hs := hstep N (Nat.lt_succ_self N)
    have hb' := mul_le_mul_of_nonneg_right hr1 (show 0≤(N:ℝ)*b by positivity)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

lemma exp_neg_two_le {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) : exp (-2*x)≤1-x := by
  have hpos : 0<1-x := by linarith
  have hi : (1-x)⁻¹≤1+2*x := by
    rw [inv_eq_one_div,div_le_iff₀ hpos]
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hh : -2*x≤log (1-x) := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

lemma pow_one_sub_lower {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) (N : ℕ) :
    exp (-2*(N:ℝ)*x)≤(1-x)^N := by
  have hh := pow_le_pow_left₀ (exp_pos (-2*x)).le (exp_neg_two_le hx hx1) N
  rw [←Real.exp_nat_mul] at hh
  convert! hh using 1
  congr 1
  ring

lemma entropy_retention_mesh (p : Prior α) (hp : ∀ x,0<p x) (f : α → ℝ) (hf : ∀ x,0<f x)
    {C K : ℝ} (hC : 0<C) (hK : 0≤K)
    (hbound : ∀ q : Prior α, ∀ x y, |Channel.interaction v q x y| ≤ K)
    {N : ℕ} (hN : 0<N) (hCN : 4*C≤N) (hKN : K≤N)
    (hvar : ∀ k<N, ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p (N:ℝ)⁻¹ h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2)) :
    exp (-4*C)*ent p f-4*K^2/(N:ℝ)*avg p f ≤ remainingEntropy v p f (N:ℝ)⁻¹ N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have ht : (0:ℝ) ≤ (N:ℝ)⁻¹ := inv_nonneg.mpr hn.le
  have hc : 2*C*(N:ℝ)⁻¹≤1/2 := by
    rw [←div_eq_mul_inv,div_le_iff₀ hn]
    linarith
  have hk : K*(N:ℝ)⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_iff₀ hn,one_mul]
    exact hKN
  have hs := affine_lower (remainingEntropy v p f (N:ℝ)⁻¹)
    (by linarith : 0≤1-2*C*(N:ℝ)⁻¹) (by nlinarith [mul_nonneg hC.le ht] : 1-2*C*(N:ℝ)⁻¹≤1)
    (mul_nonneg (by positivity) (avg_pos p hf).le : 0≤4*K^2*((N:ℝ)⁻¹)^2*avg p f) N
    (fun k hkn => entropy_recurrence v p hp f hf hC ht hK hbound hk k (hvar k hkn))
  rw [remainingEntropy_zero] at hs
  have he : (N:ℝ)*(4*K^2*((N:ℝ)⁻¹)^2*avg p f)=4*K^2/(N:ℝ)*avg p f := by
    field_simp [hn.ne']
  have hh := pow_one_sub_lower (mul_nonneg (by positivity : 0≤2*C) ht) hc N
  have hee : -2*(N:ℝ)*(2*C*(N:ℝ)⁻¹) = -4*C := by field_simp [hn.ne'];ring
  rw [hee] at hh
  rw [he] at hs
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right hh (ent_nonneg p hf)) _).trans hs

theorem entropy_of_observation_estimates (p : Prior α) (hp : ∀ x,0<p x)
    (f : α → ℝ) (hf : ∀ x,0<f x) {C E : ℝ} (hC : 0<C)
    (hvar : ∀ N : ℕ, 0<N → ∀ k<N, ∀ h : History d k, ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt (posterior v p (N:ℝ)⁻¹ h) (linear v a) s) (linear v a) ≤ C*(∑ i,a i^2))
    (hterminal : ∀ N : ℕ, 0<N → remainingEntropy v p f (N:ℝ)⁻¹ N ≤ E) :
    exp (-4*C)*ent p f ≤ E := by
  obtain ⟨K,hK,hbound⟩ := Channel.exists_interaction_bound v
  have hinv : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => E+4*K^2/(N:ℝ)*avg p f) atTop (𝓝 E) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,add_zero] using
      tendsto_const_nhds.add ((tendsto_const_nhds.mul hinv).mul_const (avg p f))
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4*C)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop K)] with N hn hc hk
  have hh := (entropy_retention_mesh v p hp f hf hC hK hbound hn hc hk (hvar N hn)).trans
    (hterminal N hn)
  linarith only [hh]

end History
end SKRatio.Observation

end
end

end OAI
