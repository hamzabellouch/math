import OAI.Combinatorics.HadwigerCounterexample.FiniteEntropy
import OAI.Combinatorics.HadwigerCounterexample.WalshBounds

namespace OAI

/-! # Relative Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

def lsupp (p q : Wgt A) := ∀ x,p x ≠ 0 → q x≠0

def tension (p q : Wgt A) := avg p (fun x => log (p x)-log (q x))
def varOne (p q : Wgt A) := ∑ x, |p x-q x|

theorem tension_of_ratio {p q : Wgt A} (h : lsupp p q) :
    tension p q=avg p (fun x => log (p x/q x)) :=
  avg_congr (fun i hi => (Real.log_div hi (h i hi)).symm)

theorem tension_as_diff (p q : Wgt A) :
    tension p q= negEnt p-avg p (fun x => log (q x)) := avg_sub p _ _

theorem tension_mix {μ : Wgt A} {f : A→Wgt B} (q : Wgt B) :
    avg μ (fun x => tension (f x) q) =
      avg μ (fun x => tension (f x) (mixW μ f))+tension (mixW μ f) q := by
  let u := mixW μ f
  have h (x : A) : tension (f x) q=tension (f x) u+
      avg (f x) (fun i => log (u i)-log (q i)) := by
    simp only [tension_as_diff,avg_sub]
    ring
  simp_rw [h,avg_add,← mixW_avg]; rfl

theorem tension_le_cap {p q : Wgt A} (hp : ∀ i,0 ≤ p i) (hq : ∀ i,0 ≤ q i)
    (C : ℝ) (hc : 0<C) (h : ∀ i,p i≤ C*q i) :
    tension p q≤tot p*log C := by
  rw [←avg_const]
  unfold tension avg
  refine sum_le_sum fun i _ => ?_
  rcases eq_or_lt_of_le (hp i) with h'|h'
  · rw [←h']; simp
  have hqi : q i ≠ 0 :=
    (pos_of_mul_pos_right (h'.trans_le (h i)) hc.le).ne'
  have hg : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
  refine mul_le_mul_of_nonneg_left ?_ h'.le
  change log (p i) - log (q i) ≤ log C
  rw [← Real.log_div h'.ne' hg.ne']
  exact Real.log_le_log (by positivity) ((div_le_iff₀ hg).mpr (h i))

private theorem tension_cell (a b : ℝ) (ha : 0≤a) (hb : 0 ≤ b) (h : a≠0→b≠0) :
    (√a-√b)^2 ≤ a*(log a - log b)+ b - a := by
  rcases eq_or_lt_of_le ha with h'|h'
  · rw [← h']; simp only [sqrt_zero,zero_sub,neg_sq,zero_mul,zero_add,sub_zero]; rw [sq_sqrt hb]
  have hb' := lt_of_le_of_ne hb (Ne.symm (h h'.ne'))
  have hc : 0<√a := by positivity
  have ht := Real.log_le_sub_one_of_pos (x:=√b/√a) (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hb,Real.log_sqrt ha] at ht
  have hh := mul_le_mul_of_nonneg_right ht ha
  have he : √b/√a*a = √b*√a := by
    field_simp; rw [sq_sqrt ha]
  rw [sub_mul,sub_mul,he] at hh
  nlinarith only [hh,sq_sqrt ha,sq_sqrt hb]

set_option maxHeartbeats 600000 in
theorem var_tension (p q : Wgt A) (hp : IsLaw p) (hq : IsLaw q) (h : lsupp p q) :
    varOne p q ^ 2 ≤ tension p q * 4 := by
  let a (i : A) := |√(p i)-√(q i)|
  let b (i : A) := √(p i)+√(q i)
  have ha : ∑ i, a i ^ 2 ≤ tension p q := by
    have ht (x : A) :
        a x ^2 ≤ p x * (log (p x)-log (q x))+q x-p x := by
      unfold a; rw [sq_abs]; exact tension_cell _ _ (hp.nz _) (hq.nz _) (h _)
    refine (sum_le_sum (fun i (_: i∈univ) => ht i)).trans_eq ?_
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    change _ +tot q-tot p=tension p q
    rw [hp.total,hq.total,add_sub_cancel_right]
    rfl
  have hb : ∑ i,b i^2 ≤ 4 := by
    have ht (x : A) :
        b x ^ 2 ≤ 2*p x+2*q x := by
      unfold b; nlinarith only [sq_sqrt (hp.nz x),sq_sqrt (hq.nz x),
        sq_nonneg (√(p x)-√(q x))]
    refine (sum_le_sum (fun i (_: i∈univ) => ht i)).trans_eq ?_
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    change 2*tot p + 2*tot q = 4
    rw [hp.total,hq.total]
    norm_num
  have h0 : 0≤tension p q := le_trans (sum_nonneg (fun i _ => sq_nonneg _)) ha
  have he : varOne p q = ∑ i, a i * b i := by
    unfold varOne
    refine sum_congr rfl (fun i _ => ?_)
    have hy :
        (√(p i)-√(q i))*b i=p i-q i := by
      unfold b; nlinarith only [sq_sqrt (hp.nz i),sq_sqrt (hq.nz i)]
    rw [← hy,abs_mul,abs_of_nonneg (show 0≤b i from by unfold b; positivity)]
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq ..).trans
    (mul_le_mul ha hb (sum_nonneg (fun i _ => sq_nonneg _)) h0)

theorem tension_nonneg {p q : Wgt A} (hp : IsLaw p) (hq : IsLaw q) (h : lsupp p q) :
    0 ≤ tension p q := by nlinarith only [var_tension p q hp hq h,sq_nonneg (varOne p q)]
end HadwigerCounterexample

end

end OAI
