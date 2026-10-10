import Mathlib
import OAI.Probability.SKGap.Localization.DriftSquare
import OAI.Probability.SKGap.Localization.Envelope
import OAI.Probability.SKGap.Localization.AffineUpper

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep DiscreteRecurrence
noncomputable section
variable {n : ℕ}

lemma entropy_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B : ∀k,Set (History n k)) (hB : ∀k,MeasurableSet (B k))
    (W A a T : ℝ) (hW : 0≤W) (hA : 0≤A) (ha : 0<a) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hgood : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t K≤
      exp (4*T/a)*(T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*T*t) := by
  have hh:=affine_upper (entropy p (squarePrior p f hf) t)
    (show 0≤4*t/a by positivity)
    (show 0≤t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 by have := energy_nonneg p f; positivity)
    (entropy_zero p (squarePrior p f hf) t).le K
    (fun k hk => by
      simpa only [add_assoc] using entropy_good_step p hp f hf ht htn k (B k) (hB k) W A a hW hA ha
        (hsmall k hk) (hgood k hk))
  have he : (K:ℝ)*(4*t/a)=4*T/a := by rw [←hT]; ring
  rw [he] at hh
  convert hh using 1
  rw [←hT]
  ring

lemma envelope_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (K : ℕ)
    (G : ∀k,Set (History n k)) (hG : ∀k,MeasurableSet (G k))
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (D T : ℝ) (hD : 0≤D) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hgood : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    exp (-2*D*T)*var p f≤ envelopeIntegral p t (G K) f+D*T*energy p f+
      16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2) := by
  have hh:=affine_lower (fun k => envelopeIntegral p t (G k) f)
    (show 0≤1-D*t by linarith) (show 1-D*t≤1 by nlinarith)
    (show 0≤D*t*energy p f+16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) by
      have := energy_nonneg p f
      have := avg_nonneg p (fun x => (f x)^2) (fun _ => sq_nonneg _)
      positivity) K (fun k hk => by
        have hs:=envelope_step_bound p hp (G k) (hG k) (G (k+1)) (hG (k+1))
          (hprefix k hk) f ht htn D hD (hgood k hk)
        linarith)
  have hz:=mul_le_mul_of_nonneg_left (variance_le_envelope_zero p t (G 0) f)
    (pow_nonneg (show 0≤1-D*t by linarith) K)
  have he:=mul_le_mul_of_nonneg_right (pow_one_sub_lower (mul_nonneg hD ht) hDt K) (var_nonneg p f)
  have heq : -2*(K:ℝ)*(D*t)= -2*D*T := by rw [←hT]; ring
  rw [heq] at he
  rw [←hT]
  rw [←hT] at he
  nlinarith

theorem localization_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    b*(n:ℝ)*exp (-2*D*T)*var p f ≤
      b*(n:ℝ)*((D*T+L)*energy p f+16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2))+
      avg p (fun x => (f x)^2)*(exp (4*T/a)*(T*(W*(n:ℝ)+
        A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+64*(n:ℝ)^2*T*t)+1) := by
  have hv:=envelope_bound p hp f ht htn K G hG hprefix D T hD hDt hT hcov
  have hterm:=envelope_terminal_bound p hp f hf ht (G K) E (hG K) hE hGE L hL hterminal
  have hentropy:=entropy_bound p hp f hf ht htn K B hB W A a T hW hA ha hT hsmall hmean
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht K E hE (b*(n:ℝ))
    (by simpa only [neg_mul] using hEsmall)
  have heN:=mul_le_mul_of_nonneg_left he hf.le
  have hvb:=mul_le_mul_of_nonneg_left hv (show 0≤b*(n:ℝ) by positivity)
  have htb:=mul_le_mul_of_nonneg_left hterm (show 0≤b*(n:ℝ) by positivity)
  have hHN:=mul_le_mul_of_nonneg_left hentropy hf.le
  nlinarith

end
end SKGap.GaussianHistory

end OAI
