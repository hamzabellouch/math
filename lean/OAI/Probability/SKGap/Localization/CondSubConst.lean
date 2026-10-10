import Mathlib
import OAI.Probability.SKGap.Entropy.EntropyBound

namespace OAI

namespace SKGap.GaussianStep
open scoped BigOperators
noncomputable section
variable {n : ℕ}

lemma cond_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ)
    (i : Fin n) (x : Spin n) : cond p i (fun x => f x-c) x=cond p i f x-c := by
  unfold cond
  field_simp [(add_pos (hp x) (hp (flip i x))).ne']
  ring

lemma energy_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ) :
    energy p (fun x => f x-c)=energy p f := by
  unfold energy
  simp_rw [cond_sub_const p hp f c,sub_sub_sub_cancel_right]

lemma var_center (p : Prior n) (f : Spin n→ℝ) :
    var p (fun x => f x-avg p f)=var p f := by
  unfold var
  rw [avg_center]
  simp only [sub_zero]

end
end SKGap.GaussianStep

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma localization_scalar {den N E r c e s v w : ℝ} (hd : 0<den) (hN : 0<N)
    (H : den*r*N≤den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) :
    (r-(e+(s*v+1)/den))*N≤(c+s*w/den)*E := by
  have he : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)=
      den*r*N-(den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) := by
    field_simp
    ring
  have hh : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)≤0 := by
    rw [he]
    linarith
  have hz : (r-(e+(s*v+1)/den))*N-(c+s*w/den)*E ≤ 0 := by
    by_contra hz
    have hm := mul_pos hd (lt_of_not_ge hz)
    linarith
  linarith

def localizationLoss (n : ℕ) (t W A a b T : ℝ) : ℝ :=
  16*(n:ℝ)^2*T*t+(exp (4*T/a)*(T*(W*(n:ℝ)+2*A*sqrt (n:ℝ)+4/a)+64*(n:ℝ)^2*T*t)+1)/(b*(n:ℝ))

def localizationCost (n : ℕ) (A a b D L T : ℝ) : ℝ :=
  D*T+L+exp (4*T/a)*T*A*sqrt (n:ℝ)/(b*(n:ℝ))

lemma centered_localization_bound (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)) (hc : avg p f=0)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
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
    (exp (-2*D*T)-localizationLoss n t W A a b T)*var p f≤
      localizationCost n A a b D L T*energy p f := by
  have hh:=localization_bound p hp f hf ht htn K B G hB hG E hE hprefix hGE
    D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall hmean hcov hterminal
  have hv : var p f=avg p (fun x => (f x)^2) := by rw [var_eq,hc]; ring
  rw [hv] at hh ⊢
  let v:=T*(W*(n:ℝ)+2*A*sqrt (n:ℝ)+4/a)+64*(n:ℝ)^2*T*t
  let w:=T*A*sqrt (n:ℝ)
  have hbody : T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
      64*(n:ℝ)^2*T*t = v+w*energy p f/avg p (fun x => (f x)^2) := by dsimp [v,w]; ring
  rw [hbody] at hh
  simpa only [localizationLoss,localizationCost,v,w,mul_assoc] using
    localization_scalar (mul_pos hb (by exact_mod_cast hn)) hf hh

theorem poincare_of_history_estimates (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T C : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hC : 0≤C)
    (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀(f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)),∀k<K,∀h:History n k,h∉B k →
      driftSquare p (squarePrior p f hf) t h ≤
        W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀(f : Spin n→ℝ),∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀(f : Spin n→ℝ),∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f)
    (hLoss : localizationLoss n t W A a b T≤exp (-2*D*T)/2)
    (hCost : localizationCost n A a b D L T≤C) :
    ∀f : Spin n→ℝ,var p f≤(2*C/exp (-2*D*T))*energy p f := by
  intro f
  by_cases hv : 0<var p f
  · let F:=fun x => f x-avg p f
    have hF : 0<avg p (fun x => (F x)^2) := hv
    have hh:=centered_localization_bound p hp hn F hF (avg_center p f) ht htn K B G hB hG E hE hprefix hGE
      D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall (hmean F hF) (hcov F) (hterminal F)
    dsimp [F] at hh
    rw [var_center,energy_sub_const p hp] at hh
    have hl:=mul_le_mul_of_nonneg_right hLoss hv.le
    have hc:=mul_le_mul_of_nonneg_right hCost (energy_nonneg p f)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (exp_pos (-2*D*T))).mpr
    nlinarith
  · have hz : var p f=0 := le_antisymm (le_of_not_gt hv) (var_nonneg p f)
    rw [hz]
    exact mul_nonneg (div_nonneg (by positivity) (exp_pos _).le) (energy_nonneg p f)

end
end SKGap.GaussianHistory

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma eventProbability_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ}
    (E : Set (History n k)) (hE : MeasurableSet E) :
    eventProbability p t (Prod.fst ⁻¹' E : Set (History n (k+1)))=eventProbability p t E := by
  rw [eventProbability, ← integral_indicator (hE.preimage measurable_fst),
    eventProbability, ← integral_indicator hE]
  have hm : Measurable (E.indicator (fun _=> (1:ℝ))) := measurable_const.indicator hE
  have he (h : History n k) : density p t h*E.indicator (fun _=>(1:ℝ)) h=E.indicator (density p t) h := by
    by_cases hmem : h∈E <;> simp [hmem]
  have hi : Integrable (fun h=>density p t h*E.indicator (fun _=> (1:ℝ)) h) (reference n k) := by
    simpa only [he] using (integrable_density p t k).indicator hE
  have H:=integral_lift p ht _ hm hi
  have he' (h : History n (k+1)) : density p t h*E.indicator (fun _=>(1:ℝ)) h.1=
      (Prod.fst ⁻¹' E).indicator (density p t (k:=k+1)) h := by
    by_cases hmem : h.1∈E <;> simp [hmem]
  simpa only [he,he'] using H

lemma eventProbability_union_le (p : Prior n) {t : ℝ} (_ht : 0≤t) {k : ℕ}
    (E F : Set (History n k)) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    eventProbability p t (E∪F)≤eventProbability p t E+eventProbability p t F := by
  have H := measureReal_union_le (μ := law p t k) E F
  have he (A : Set (History n k)) (hA : MeasurableSet A) :
      (law p t k).real A=eventProbability p t A := by
    rw [Measure.real, ← eventProbability_eq p t A hA, ENNReal.toReal_ofReal (eventProbability_nonneg p t A)]
  simpa only [he _ (hE.union hF),he E hE,he F hF] using H

def goodPrefix (B : ∀k, Set (History n k)) : ∀k,Set (History n k)
  | 0 => (B 0)ᶜ
  | k+1 => (Prod.fst ⁻¹' goodPrefix B k) ∩ (B (k+1))ᶜ

lemma measurable_goodPrefix (B : ∀k, Set (History n k)) (hB : ∀k,MeasurableSet (B k)) :
    ∀k,MeasurableSet (goodPrefix B k)
  | 0 => (hB 0).compl
  | k+1 => ((measurable_goodPrefix B hB k).preimage measurable_fst).inter (hB (k+1)).compl

lemma goodPrefix_not_bad (B : ∀k, Set (History n k)) :
    ∀k,∀h:History n k,h∈goodPrefix B k→h∉B k
  | 0, _, h => h
  | _+1, _, h => h.2

lemma goodPrefix_previous (B : ∀k, Set (History n k)) (k : ℕ)
    (h : History n (k+1)) (hh : h∈goodPrefix B (k+1)) : h.1∈goodPrefix B k := hh.1

lemma goodPrefix_failure_bound (p : Prior n) {t : ℝ} (ht : 0≤t)
    (B : ∀k,Set (History n k)) (hB : ∀k,MeasurableSet (B k)) :
    ∀k,eventProbability p t (goodPrefix B k)ᶜ ≤ ∑i∈Finset.range (k+1),eventProbability p t (B i)
  | 0 => by simp [goodPrefix]
  | k+1 => by
    have hE : (goodPrefix B (k+1))ᶜ =
        (Prod.fst ⁻¹' (goodPrefix B k)ᶜ) ∪ B (k+1) := by
          ext h
          simp only [goodPrefix,mem_compl_iff,mem_preimage,mem_inter_iff,mem_union]
          tauto
    rw [hE,Finset.sum_range_succ]
    have H : eventProbability p t (Prod.fst ⁻¹' (goodPrefix B k)ᶜ : Set (History n (k+1))) ≤
        ∑i∈Finset.range (k+1),eventProbability p t (B i) := by
      rw [eventProbability_lift p ht _ (measurable_goodPrefix B hB k).compl]
      exact goodPrefix_failure_bound p ht B hB k
    exact (eventProbability_union_le p ht _ _
      ((measurable_goodPrefix B hB k).compl.preimage measurable_fst) (hB (k+1))).trans
        (by linarith)

lemma eventProbability_mono (p : Prior n) {t : ℝ} (_ht : 0≤t) {k : ℕ}
    {E F : Set (History n k)} (h : E⊆F) : eventProbability p t E≤eventProbability p t F := by
  exact setIntegral_mono_set (integrable_density p t k).integrableOn
    (ae_of_all _ (fun h=> (density_pos p t h).le)) (Filter.Eventually.of_forall h)

lemma bad_term_le_sum (p : Prior n) (t : ℝ) (B : ∀k,Set (History n k)) {k K : ℕ}
    (hk : k≤K) : eventProbability p t (B k)≤∑i∈Finset.range (K+1),eventProbability p t (B i) := by
  exact Finset.single_le_sum (fun i _=>eventProbability_nonneg p t (B i)) (by simpa using hk)

end
end SKGap.GaussianHistory

end OAI
