import Mathlib
import OAI.Probability.SKRatio.FiniteChain.EntropicCovariance

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
variable {α : Type*} [Fintype α]

def logRemainder (u a : ℝ) : ℝ := u*log (u/a)-u+a

lemma logRemainder_nonneg {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    0 ≤ logRemainder u a := by
  have h := mul_le_mul_of_nonneg_left
    (self_sub_one_le_mul_log (div_nonneg hu.le ha.le)) ha.le
  have he : a*(u/a*log (u/a))-(a*(u/a-1)) = logRemainder u a := by
    unfold logRemainder
    field_simp [ha.ne']
    ring
  rw [← he]
  linarith only [h]

lemma logRemainder_eq {u a : ℝ} (hu : u ≠ 0) (ha : a ≠ 0) :
    logRemainder u a = u*log u-u*log a-u+a := by
  rw [logRemainder,log_div hu ha]
  ring

lemma ent_nonneg (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 < f x) : 0 ≤ ent p f := by
  have hj := convexOn_mul_log.map_sum_le (t := Finset.univ) (w := p.mass) (p := f)
    (fun x _ => p.nonneg x) p.sum_one (fun x _ => (hf x).le)
  change avg p f*log (avg p f) ≤ avg p (fun x => f x*log (f x)) at hj
  unfold ent FiniteLaw.entropy
  exact sub_nonneg.mpr hj

lemma avg_sum (p : Prior α) {ι : Type*} [Fintype ι] (f : ι → α → ℝ) :
    avg p (fun x => ∑ i, f i x) = ∑ i, avg p (f i) := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma avg_logRemainder (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) {a : ℝ} (ha : 0<a) :
    avg p (fun x => logRemainder (f x) a) = ent p f+logRemainder (avg p f) a := by
  simp_rw [logRemainder_eq (hf _).ne' ha.ne']
  rw [avg_add,avg_sub,avg_sub,avg_mul_const,avg_const,
    logRemainder_eq (avg_pos p hf).ne' ha.ne']
  unfold ent FiniteLaw.entropy
  change _ = avg p (fun x => f x*log (f x))-avg p f*log (avg p f)+_
  ring

lemma ent_minimizes (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) {a : ℝ} (ha : 0<a) :
    ent p f ≤ avg p (fun x => logRemainder (f x) a) := by
  rw [avg_logRemainder p f hf ha]
  exact le_add_of_nonneg_right (logRemainder_nonneg (avg_pos p hf) ha)

lemma ent_eq_remainder (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    ent p f = avg p (fun x => logRemainder (f x) (avg p f)) := by
  rw [avg_logRemainder p f hf (avg_pos p hf)]
  simp only [logRemainder,div_self (avg_pos p hf).ne',log_one,mul_zero,zero_sub,neg_add_cancel,add_zero]

lemma prior_le_one (p : Prior α) (x : α) : p x ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

lemma ent_bound (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    ent p f ≤ ∑ x, logRemainder (f x) 1 := by
  apply (ent_minimizes p f hf zero_lt_one).trans
  exact Finset.sum_le_sum (fun x _ => mul_le_of_le_one_left
    (logRemainder_nonneg (hf x) zero_lt_one) (prior_le_one p x))

lemma continuous_entropy_masses (f : α → ℝ) :
    Continuous (fun p : α → ℝ => FiniteLaw.entropy p f) := by
  have hs : Continuous (fun p : α → ℝ => FiniteLaw.mean p f) :=
    continuous_finsetSum _ (fun x _ => (continuous_apply x : Continuous (fun p : α → ℝ => p x)).mul_const (f x))
  exact (continuous_finsetSum _ (fun x _ => (continuous_apply x : Continuous (fun p : α → ℝ => p x)).mul_const (f x*log (f x)))).sub
    (continuous_mul_log.comp hs)

lemma avg_ent_eq_remainder (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) :
    ent p f = avg p (fun x => f x*log (f x/avg p f)) := by
  have he (x : α) : f x*log (f x/avg p f) = f x*log (f x)-f x*log (avg p f) := by
    rw [log_div (hf x).ne' (avg_pos p hf).ne',mul_sub]
  simp_rw [he]
  rw [avg_sub,avg_mul_const]
  rfl

lemma avg_log_le_log_avg (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0<f x) :
    avg p (fun x => log (f x)) ≤ log (avg p f) := by
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
    (w := p.mass) (p := f) (fun x _ => p.nonneg x) p.sum_one (fun x _ => hf x)
  exact hj

lemma ent_le_cov_log (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    ent p f ≤ avg p (fun x => f x*log (f x))-avg p f*avg p (fun x => log (f x)) := by
  have h := mul_le_mul_of_nonneg_left (avg_log_le_log_avg p f hf) (avg_pos p hf).le
  unfold ent FiniteLaw.entropy
  change avg p (fun x => f x*log (f x))-avg p f*log (avg p f) ≤ _
  linarith only [h]

lemma logSum (p : Prior α) (a b : α → ℝ) (ha : ∀ x,0<a x) (hb : ∀ x,0<b x) :
    avg p a*log (avg p a/avg p b) ≤ avg p (fun x => a x*log (a x/b x)) := by
  let q := reweight p b hb
  have he : avg q (fun x => a x/b x) = avg p a/avg p b := by
    rw [avg_reweight]
    congr 1
    congr 1
    funext x
    field_simp [(hb x).ne']
  have hj := convexOn_mul_log.map_sum_le (t := Finset.univ) (w := q.mass)
    (p := fun x => a x/b x) (fun x _ => q.nonneg x) q.sum_one
    (fun x _ => (div_pos (ha x) (hb x)).le)
  change avg q (fun x => a x/b x)*log (avg q (fun x => a x/b x)) ≤
    avg q (fun x => (a x/b x)*log (a x/b x)) at hj
  rw [he,avg_reweight] at hj
  have he₂ : (fun x => b x*(a x/b x*log (a x/b x))) =
      fun x => a x*log (a x/b x) := by
    funext x
    field_simp [(hb x).ne']
  rw [he₂] at hj
  have h := mul_le_mul_of_nonneg_right hj (avg_pos p hb).le
  convert! h using 1 <;> field_simp [(avg_pos p hb).ne']

theorem entropy_average_le {ι : Type*} [Fintype ι] (p : Prior α) (q : Prior ι)
    (f : ι → α → ℝ) (hf : ∀ i x, 0<f i x) :
    ent p (fun x => avg q (fun i => f i x)) ≤ avg q (fun i => ent p (f i)) := by
  have hswap (F : ι → α → ℝ) : avg p (fun x => avg q (fun i => F i x)) =
      avg q (fun i => avg p (F i)) := by
    simp only [avg,FiniteLaw.mean,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [avg_ent_eq_remainder p _ (fun x => avg_pos q (fun i => hf i x))]
  rw [hswap f]
  calc
    _ ≤ avg p (fun x => avg q (fun i => f i x*log (f i x/avg p (f i)))) := by
      apply avg_mono p
      intro x
      exact logSum q (fun i => f i x) (fun i => avg p (f i)) (fun i => hf i x)
        (fun i => avg_pos p (hf i))
    _ = avg q (fun i => ent p (f i)) := by
      rw [hswap]
      congr 1
      funext i
      exact (avg_ent_eq_remainder p (f i) (hf i)).symm

end SKRatio.Observation

end
end

end OAI
