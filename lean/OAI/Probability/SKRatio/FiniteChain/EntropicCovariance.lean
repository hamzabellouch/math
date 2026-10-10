import Mathlib
import OAI.Probability.SKRatio.Variational.UniformGap
import OAI.Probability.SKRatio.Entropy.Entropy

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

structure Prior (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

instance : CoeFun (Prior α) (fun _ => α → ℝ) := ⟨Prior.mass⟩

@[ext] lemma Prior.ext {p q : Prior α} (h : p.mass = q.mass) : p = q := by
  cases p; cases q; congr

def avg (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.mean p f

def var (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.variance p f

def ent (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.entropy p f

lemma avg_const (p : Prior α) (c : ℝ) : avg p (fun _ => c) = c := by
  simp only [avg,FiniteLaw.mean,← Finset.sum_mul,p.sum_one,one_mul]

lemma avg_nonneg (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

lemma avg_pos (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 < f x) : 0 < avg p f := by
  have h : 0 < ∑ x, p x := by rw [p.sum_one];norm_num
  obtain ⟨x,hx,hpx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => p.nonneg x)).mp h
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (hf y).le)
    ⟨x,hx,mul_pos hpx (hf x)⟩

lemma avg_mono (p : Prior α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : avg p f ≤ avg p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

lemma avg_add (p : Prior α) (f g : α → ℝ) : avg p (fun x => f x+g x) = avg p f+avg p g := by
  simp only [avg,FiniteLaw.mean,mul_add,Finset.sum_add_distrib]

lemma avg_sub (p : Prior α) (f g : α → ℝ) : avg p (fun x => f x-g x) = avg p f-avg p g := by
  simp only [avg,FiniteLaw.mean,mul_sub,Finset.sum_sub_distrib]

lemma avg_const_mul (p : Prior α) (c : ℝ) (f : α → ℝ) : avg p (fun x => c*f x) = c*avg p f := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum,mul_left_comm]

lemma avg_mul_const (p : Prior α) (f : α → ℝ) (c : ℝ) : avg p (fun x => f x*c) = avg p f*c := by
  simp only [avg,FiniteLaw.mean,Finset.sum_mul,mul_assoc]

lemma var_eq (p : Prior α) (v : α → ℝ) : var p v = avg p (fun x => v x^2)-(avg p v)^2 :=
  FiniteLaw.variance_eq p v p.sum_one

def tiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) : ℝ := avg p (fun x => exp (s*v x))

lemma tiltZ_pos (p : Prior α) (v : α → ℝ) (s : ℝ) : 0 < tiltZ p v s :=
  avg_pos p (fun _ => exp_pos _)

def tilt (p : Prior α) (v : α → ℝ) (s : ℝ) : Prior α where
  mass x := p x*exp (s*v x)/tiltZ p v s
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (exp_nonneg _)) (tiltZ_pos p v s).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (tiltZ_pos p v s).ne'

@[simp] lemma tilt_apply (p : Prior α) (v : α → ℝ) (s : ℝ) (x : α) :
    tilt p v s x = p x*exp (s*v x)/tiltZ p v s := rfl

@[simp] lemma tiltZ_zero (p : Prior α) (v : α → ℝ) : tiltZ p v 0 = 1 := by
  simp only [tiltZ,zero_mul,exp_zero,avg_const]

@[simp] lemma tilt_zero (p : Prior α) (v : α → ℝ) : tilt p v 0 = p := by
  ext x
  simp only [tilt_apply,zero_mul,exp_zero,tiltZ_zero,mul_one,div_one]

lemma avg_tilt (p : Prior α) (v f : α → ℝ) (s : ℝ) :
    avg (tilt p v s) f = avg p (fun x => exp (s*v x)*f x)/tiltZ p v s := by
  simp only [avg,FiniteLaw.mean,tilt_apply,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma hasDerivAt_tiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (tiltZ p v) (avg p (fun x => exp (s*v x)*v x)) s := by
  unfold tiltZ avg FiniteLaw.mean
  apply HasDerivAt.fun_sum
  intro x _
  simpa only [id_eq,one_mul] using
    (((hasDerivAt_id s).mul_const (v x)).exp).const_mul (p x)

lemma hasDerivAt_tiltNumerator (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => avg p (fun x => exp (r*v x)*v x))
      (avg p (fun x => exp (s*v x)*(v x)^2)) s := by
  unfold avg FiniteLaw.mean
  apply HasDerivAt.fun_sum
  intro x _
  convert! (((((hasDerivAt_id s).mul_const (v x)).exp).mul_const (v x)).const_mul (p x)) using 1
  simp only [id_eq,one_mul]
  ring

lemma hasDerivAt_logTiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => log (tiltZ p v r)) (avg (tilt p v s) v) s := by
  rw [avg_tilt]
  exact (hasDerivAt_tiltZ p v s).log (tiltZ_pos p v s).ne'

lemma hasDerivAt_tiltedMean (p : Prior α) (v : α → ℝ) (s : ℝ) :
    HasDerivAt (fun r => avg (tilt p v r) v) (var (tilt p v s) v) s := by
  simp_rw [avg_tilt]
  convert! (hasDerivAt_tiltNumerator p v s).div (hasDerivAt_tiltZ p v s)
    (tiltZ_pos p v s).ne' using 1
  rw [var_eq,avg_tilt,avg_tilt]
  field_simp [(tiltZ_pos p v s).ne']

lemma quadratic_upper_of_derivatives (F G Q : ℝ → ℝ) {C : ℝ}
    (hF : ∀ r, HasDerivAt F (G r) r) (hG : ∀ r, HasDerivAt G (Q r) r)
    (hQ : ∀ r, Q r ≤ C) (s : ℝ) :
    F s ≤ F 0 + s*G 0 + C*s^2/2 := by
  let A := fun r => F r-C*r^2/2
  let B := fun r => G r-C*r
  have hA (r : ℝ) : HasDerivAt A (B r) r := by
    convert! (hF r).sub ((((hasDerivAt_id r).pow 2).const_mul C).div_const 2) using 1
    dsimp [A,B]
    ring
  have hB (r : ℝ) : HasDerivAt B (Q r-C) r := by
    dsimp only [B]
    convert! (hG r).sub ((hasDerivAt_id r).const_mul C) using 1
    simp only [mul_one]
  have hanti : Antitone B := antitone_of_deriv_nonpos
    (fun r => (hB r).differentiableAt) (fun r => by rw [(hB r).deriv];linarith [hQ r])
  have hderiv : deriv A = B := funext (fun r => (hA r).deriv)
  have hconc : ConcaveOn ℝ Set.univ A := Antitone.concaveOn_univ_of_deriv
    (fun r => (hA r).differentiableAt) (hderiv ▸ hanti)
  rcases lt_trichotomy 0 s with hs | rfl | hs
  · have h := hconc.slope_le_deriv (Set.mem_univ 0) (Set.mem_univ s) hs
      (hA 0).differentiableAt
    rw [(hA 0).deriv] at h
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul] at h
    have hh : A s-A 0 ≤ B 0*s := by
      have he : s⁻¹*(A s-A 0) = (A s-A 0)/s := by ring
      rw [he,div_le_iff₀ hs] at h
      exact h
    dsimp [A,B] at hh
    nlinarith only [hh]
  · ring_nf
    exact le_rfl
  · have h := hconc.deriv_le_slope (Set.mem_univ s) (Set.mem_univ 0) hs
      (hA 0).differentiableAt
    rw [(hA 0).deriv] at h
    simp only [slope,zero_sub,vsub_eq_sub,smul_eq_mul] at h
    have hh : B 0*(-s) ≤ A 0-A s := by
      have he : (-s)⁻¹*(A 0-A s) = (A 0-A s)/(-s) := by ring
      rw [he,le_div_iff₀ (neg_pos.mpr hs)] at h
      exact h
    dsimp [A,B] at hh
    nlinarith only [hh]

theorem logTiltZ_le (p : Prior α) (v : α → ℝ) {C : ℝ}
    (hC : ∀ s, var (tilt p v s) v ≤ C) (s : ℝ) :
    log (tiltZ p v s) ≤ s*avg p v+C*s^2/2 := by
  have h := quadratic_upper_of_derivatives
    (fun r => log (tiltZ p v r)) (fun r => avg (tilt p v r) v)
    (fun r => var (tilt p v r) v) (hasDerivAt_logTiltZ p v)
    (hasDerivAt_tiltedMean p v) hC s
  simpa only [tiltZ_zero,log_one,tilt_zero,zero_add] using h

theorem mean_displacement_sq (p q : Prior α) (v : α → ℝ) {C : ℝ}
    (hp : ∀ x, 0 < p x) (hC : 0 < C) (hvar : ∀ s, var (tilt p v s) v ≤ C) :
    (avg q v-avg p v)^2 ≤ 2*C*FiniteLaw.relativeEntropy q p := by
  let d := avg q v-avg p v
  have he := FiniteLaw.entropy_variational q p (fun x => (d/C)*v x)
    q.nonneg hp q.sum_one p.sum_one
  have hm := logTiltZ_le p v hvar (d/C)
  change avg q (fun x => (d/C)*v x) ≤ FiniteLaw.relativeEntropy q p+
    log (tiltZ p v (d/C)) at he
  rw [avg_const_mul] at he
  have hh : (d/C)*d ≤ FiniteLaw.relativeEntropy q p+C*(d/C)^2/2 := by
    dsimp [d] at *
    nlinarith only [he,hm]
  have heq : (d/C)*d-C*(d/C)^2/2 = d^2/(2*C) := by field_simp;ring
  have hb : d^2/(2*C) ≤ FiniteLaw.relativeEntropy q p := by linarith only [hh,heq]
  rw [div_le_iff₀ (by positivity : 0 < 2*C)] at hb
  simpa only [mul_comm (FiniteLaw.relativeEntropy q p)] using hb

variable {ι : Type*} [Fintype ι]

def linear (v : α → ι → ℝ) (a : ι → ℝ) (x : α) : ℝ := ∑ i, a i*v x i

lemma avg_linear (p : Prior α) (v : α → ι → ℝ) (a : ι → ℝ) :
    avg p (linear v a) = ∑ i, a i*avg p (fun x => v x i) := by
  simp only [avg,FiniteLaw.mean,linear,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem vector_mean_displacement_sq (p q : Prior α) (v : α → ι → ℝ) {C : ℝ}
    (hp : ∀ x, 0 < p x) (hC : 0 < C)
    (hvar : ∀ a : ι → ℝ, ∀ s : ℝ,
      var (tilt p (linear v a) s) (linear v a) ≤ C*(∑ i, a i^2)) :
    (∑ i, (avg q (fun x => v x i)-avg p (fun x => v x i))^2) ≤
      2*C*FiniteLaw.relativeEntropy q p := by
  let a := fun i => avg q (fun x => v x i)-avg p (fun x => v x i)
  let R := ∑ i, a i^2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE := FiniteLaw.relativeEntropy_nonneg q p q.nonneg hp q.sum_one p.sum_one
  rcases eq_or_lt_of_le hR with hz | hz
  · change R ≤ _
    rw [← hz]
    exact mul_nonneg (by positivity) hE
  have hh := mean_displacement_sq p q (linear v a) hp (mul_pos hC hz) (hvar a)
  have he : avg q (linear v a)-avg p (linear v a) = R := by
    simp only [avg_linear,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    ring
  rw [he] at hh
  change R ≤ _
  nlinarith only [hh,hz]

def reweight (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) : Prior α where
  mass x := p x*f x/avg p f
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (hf x).le) (avg_pos p hf).le
  sum_one := by rw [← Finset.sum_div];exact div_self (avg_pos p hf).ne'

lemma avg_reweight (p : Prior α) (f v : α → ℝ) (hf : ∀ x, 0 < f x) :
    avg (reweight p f hf) v = avg p (fun x => f x*v x)/avg p f := by
  simp only [avg,FiniteLaw.mean,reweight,Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma relativeEntropy_reweight (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (hp : ∀ x, 0 < p x) :
    FiniteLaw.relativeEntropy (reweight p f hf) p = ent p f/avg p f := by
  have he (x : α) : p x*f x/avg p f/p x = f x/avg p f := by
    field_simp [(avg_pos p hf).ne',(hp x).ne']
  simp only [FiniteLaw.relativeEntropy,reweight,he,
    log_div (hf _).ne' (avg_pos p hf).ne',mul_sub,Finset.sum_sub_distrib]
  have ha : (∑ x, p x*f x/avg p f*log (f x)) =
      avg p (fun x => f x*log (f x))/avg p f := by
    simp only [avg,FiniteLaw.mean,Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [ha,← Finset.sum_mul,← Finset.sum_div]
  change _-avg p f/avg p f*log (avg p f)=_
  rw [div_self (avg_pos p hf).ne',one_mul]
  unfold ent FiniteLaw.entropy
  change _ = (avg p (fun x => f x*log (f x))-avg p f*log (avg p f))/avg p f
  field_simp [(avg_pos p hf).ne']

theorem covariance_entropy (p : Prior α) (v : α → ι → ℝ) (f : α → ℝ) {C : ℝ}
    (hp : ∀ x, 0 < p x) (hf : ∀ x, 0 < f x) (hC : 0 < C)
    (hvar : ∀ a : ι → ℝ, ∀ s : ℝ,
      var (tilt p (linear v a) s) (linear v a) ≤ C*(∑ i, a i^2)) :
    (∑ i, (avg p (fun x => v x i*f x)-avg p (fun x => v x i)*avg p f)^2) ≤
      2*C*avg p f*ent p f := by
  have h := vector_mean_displacement_sq p (reweight p f hf) v hp hC hvar
  rw [relativeEntropy_reweight p f hf hp] at h
  simp_rw [avg_reweight] at h
  have he (i : ι) :
      avg p (fun x => f x*v x i)/avg p f-avg p (fun x => v x i) =
      (avg p (fun x => v x i*f x)-avg p (fun x => v x i)*avg p f)/avg p f := by
    rw [show (fun x => f x*v x i) = (fun x => v x i*f x) by funext x;ring]
    field_simp [(avg_pos p hf).ne']
  simp_rw [he,div_pow] at h
  rw [← Finset.sum_div] at h
  have hm := (div_le_iff₀ (sq_pos_of_pos (avg_pos p hf))).mp h
  convert! hm using 1
  rw [pow_two]
  calc
    _ = 2*C*((ent p f/avg p f)*avg p f)*avg p f := by
      rw [div_mul_cancel₀ _ (avg_pos p hf).ne']
      ring
    _ = _ := by ring

def gibbsPrior {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : Prior (Spin n) :=
  ⟨mass g h,mass_nonneg g h,sum_mass g h⟩

lemma weight_field_tilt {n : ℕ} (g : Disorder n) (h a : Fin n → ℝ) (s : ℝ) (x : Spin n) :
    weight g (h+s • a) x = weight g h x*exp (s*Fields.linearObservable a x) := by
  rw [weight,weight,← exp_add]
  congr 1
  simp only [hamiltonian,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,Fields.linearObservable,Finset.mul_sum,mul_assoc]
  ring

lemma tilt_gibbs_linear {n : ℕ} (g : Disorder n) (h a : Fin n → ℝ) (s : ℝ) :
    tilt (gibbsPrior g h) (Fields.linearObservable a) s = gibbsPrior g (h+s • a) := by
  have hz : tiltZ (gibbsPrior g h) (Fields.linearObservable a) s =
      partition g (h+s • a)/partition g h := by
    simp only [tiltZ,avg,FiniteLaw.mean,gibbsPrior,mass,partition,weight_field_tilt,
      Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  apply Prior.ext
  funext x
  rw [tilt_apply,hz]
  simp only [gibbsPrior,mass,weight_field_tilt]
  field_simp [(partition_pos g h).ne',(partition_pos g (h+s • a)).ne']

theorem spin_covariance_entropy {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (f : Spin n → ℝ) {C : ℝ} (hf : ∀ x, 0 < f x) (hC : 0 < C)
    (hvar : ∀ θ a : Fin n → ℝ,
      Fields.variance g θ (Fields.linearObservable a) ≤ C*∑ i, a i^2) :
    (∑ i, (avg (gibbsPrior g h) (fun x => spinValue (x i)*f x)-
      avg (gibbsPrior g h) (fun x => spinValue (x i))*avg (gibbsPrior g h) f)^2) ≤
      2*C*avg (gibbsPrior g h) f*ent (gibbsPrior g h) f := by
  apply covariance_entropy (gibbsPrior g h) (fun x i => spinValue (x i)) f
    (mass_pos g h) hf hC
  intro a s
  change var (tilt (gibbsPrior g h) (Fields.linearObservable a) s) (Fields.linearObservable a) ≤ _
  rw [tilt_gibbs_linear]
  exact hvar (h+s • a) a

end SKRatio.Observation

end
end

end OAI
