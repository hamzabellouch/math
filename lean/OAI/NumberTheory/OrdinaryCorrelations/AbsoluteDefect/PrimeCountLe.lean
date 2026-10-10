import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RationalApproximation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinaryTwistWidthBasic

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryTwistWidth
open OrdinaryCorrelations OrdinaryInitialWidth OrdinaryLocalAdditive Finset Filter MeasureTheory

lemma primeCount_le (P : Finset ℕ) (n : ℕ) : primeCount P n≤P.card := card_filter_le _ _

lemma primeCount_mul (P : Finset ℕ) (hP : ∀p∈P, Nat.Prime p) {m n : ℕ}
    (hcop : m.Coprime n) : primeCount P (m*n)=primeCount P m+primeCount P n := by
  classical
  have he : P.filter (fun p=>p∣m*n)=P.filter (fun p=>p∣m)∪P.filter (fun p=>p∣n) := by
    ext p
    by_cases hp : p∈P
    · simp only [mem_filter,Finset.mem_union,hp,true_and,(hP p hp).dvd_mul]
    · simp [hp]
  have hd : Disjoint (P.filter (fun p=>p∣m)) (P.filter (fun p=>p∣n)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hdiv := Nat.dvd_gcd (mem_filter.mp hp).2 (mem_filter.mp hq).2
    rw [hcop.gcd_eq_one] at hdiv
    have he1 := Nat.eq_one_of_dvd_one hdiv
    exact (hP p (mem_filter.mp hp).1).ne_one he1
  unfold primeCount
  rw [he,card_union_of_disjoint hd]

lemma primeCount_prime_outside (P : Finset ℕ) (hP : ∀p∈P, Nat.Prime p)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) : primeCount P p=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hqP,hqp⟩ := mem_filter.mp hq
  have he : q=p := (Nat.dvd_prime hp).mp hqp |>.resolve_left (hP q hqP).ne_one
  exact hpP (he ▸ hqP)

lemma twist_oneBounded {f : ℕ→ℂ} (hf : OneBounded f) (P : Finset ℕ) (t : ℝ) :
    OneBounded (twist f P t) := by
  intro n
  simpa only [twist,norm_mul,norm_phase,mul_one] using hf n

lemma twist_multiplicative {f : ℕ→ℂ} (hf : Multiplicative f)
    (P : Finset ℕ) (hP : ∀p∈P, Nat.Prime p) (t : ℝ) :
    Multiplicative (twist f P t) := by
  intro m n hm hn hcop
  unfold twist
  rw [hf m n hm hn hcop,primeCount_mul P hP hcop,Nat.cast_add,mul_add,phase_add]
  ring

lemma twist_nonpretentious {f : ℕ→ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (P : Finset ℕ)
    (hP : ∀p∈P, Nat.Prime p) (t : ℝ) :
    UniformlyNonpretentious (twist f P t) := by
  apply PretentiousStability.uniformlyNonpretentious_change f (twist f P t)
    hf (twist_oneBounded hf P t) P _ hNP
  intro p hp hpP
  simp [twist,primeCount_prime_outside P hP hp hpP,phase]

lemma twist_fract (f : ℕ→ℂ) (P : Finset ℕ) (t : ℝ) :
    twist f P t=twist f P (Int.fract t) := by
  funext n
  unfold twist
  rw [OrdinaryUniformWidth.phase_fract]

lemma twist_sub_le {f : ℕ→ℂ} (hf : OneBounded f) (P : Finset ℕ) (s t : ℝ) (n : ℕ) :
    ‖twist f P s n-twist f P t n‖≤2*Real.pi*P.card*|s-t| := by
  unfold twist
  rw [←mul_sub,norm_mul]
  calc
    _ ≤ 1*‖phase (s*primeCount P n)-phase (t*primeCount P n)‖ :=
      mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)
    _ ≤ 2*Real.pi*|s*(primeCount P n)-t*primeCount P n| := by
      simpa only [one_mul] using phase_sub_le (s*primeCount P n) (t*primeCount P n)
    _ = 2*Real.pi*(primeCount P n)*|s-t| := by
      rw [←sub_mul,abs_mul,show |((primeCount P n):ℝ)|=(primeCount P n) from
        abs_of_nonneg (Nat.cast_nonneg _)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast primeCount_le P n

end OrdinaryTwistWidth

end

end OAI
