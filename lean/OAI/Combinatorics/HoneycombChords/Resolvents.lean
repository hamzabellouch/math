import OAI.Combinatorics.HoneycombChords.Pollaczek

namespace OAI

/-!
# Jacobi resolvents and rational Christoffel kernels

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real
noncomputable def jacobiA (n : ℕ) : ℝ := (2*n+1)*(2*n+2)/4
noncomputable def jacobiB (n : ℕ) : ℝ := ((2*n+1)^2+(2*n)^2)/4
lemma jacobiA_pos (n : ℕ) : 0 < jacobiA n := by unfold jacobiA;positivity
lemma jacobi_zero (x : ℝ) :
    x*(evenPoly (-1) 0).eval x=jacobiA 0*(evenPoly (-1) 1).eval x+
      jacobiB 0*(evenPoly (-1) 0).eval x := by
  rw [eval_evenPoly_succ (-1) x 0]
  norm_num [jacobiA,jacobiB]
  ring
lemma jacobi_succ (n : ℕ) (x : ℝ) :
    x*(evenPoly (-1) (n+1)).eval x=
      jacobiA (n+1)*(evenPoly (-1) (n+2)).eval x+
      jacobiB (n+1)*(evenPoly (-1) (n+1)).eval x+
      jacobiA n*(evenPoly (-1) n).eval x := by
  rw [show n+2=(n+1)+1 by omega,eval_evenPoly_succ (-1) x (n+1),
    eval_oddPoly_succ (-1) x n,eval_evenPoly_succ (-1) x n]
  have h1 : (2*(n:ℝ)+2) ≠ 0 := by positivity
  have h2 : (2*((n:ℝ)+1)+2) ≠ 0 := by positivity
  have h3 : (2*(n:ℝ)+3) ≠ 0 := by positivity
  simp only [jacobiA,jacobiB,Nat.cast_add,Nat.cast_one]
  field_simp
  ring
lemma jacobi_poly_zero :
    X*evenPoly (-1) 0=jacobiA 0 • evenPoly (-1) 1+jacobiB 0 • evenPoly (-1) 0 := by
  apply Polynomial.funext
  intro x
  simpa using jacobi_zero x
lemma jacobi_poly_succ (n : ℕ) :
    X*evenPoly (-1) (n+1)=jacobiA (n+1) • evenPoly (-1) (n+2)+
      jacobiB (n+1) • evenPoly (-1) (n+1)+jacobiA n • evenPoly (-1) n := by
  apply Polynomial.funext
  intro x
  simpa using jacobi_succ n x
noncomputable def negativeEval (s : ℝ) (n : ℕ) : ℝ := meixnerCoeff s (2*n)
lemma negativeEval_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < negativeEval s n :=
  meixnerCoeff_pos hs _
@[simp] lemma negativeEval_zero (s : ℝ) : negativeEval s 0=1 := rfl
lemma negativeEval_jacobi_zero (s : ℝ) :
    jacobiA 0*negativeEval s 1=(s^2+jacobiB 0)*negativeEval s 0 := by
  have h:=jacobi_zero (-(s^2))
  simp only [evenPoly_negative_eval] at h
  norm_num at h
  simp only [show meixnerCoeff s 0=1 from rfl] at h
  dsimp [negativeEval]
  linear_combination h
lemma negativeEval_jacobi_succ (s : ℝ) (n : ℕ) :
    jacobiA (n+1)*negativeEval s (n+2)=(s^2+jacobiB (n+1))*negativeEval s (n+1)-
      jacobiA n*negativeEval s n := by
  have h:=jacobi_succ n (-(s^2))
  simp only [evenPoly_negative_eval] at h
  simp only [pow_add,pow_one,neg_one_sq,mul_one,mul_neg,neg_mul] at h
  have hn : (-1:ℝ)^n ≠ 0 := by positivity
  dsimp [negativeEval]
  apply (mul_left_cancel₀ hn)
  linear_combination -h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real MeasureTheory
lemma rational_sech_integrable {Y : ℝ} (hY : 0 < Y) (k : ℕ) (P : Polynomial ℝ) :
    IntegrableOn (fun p:ℝ=>P.eval (p^2)/(p^2+Y^2)^k/Real.cosh (Real.pi*p)) (Set.Ioi 0) := by
  have hd (p : ℝ) : 0 < p^2+Y^2 := by positivity
  have hm : Continuous (fun p:ℝ=>P.eval (p^2)/(p^2+Y^2)^k/Real.cosh (Real.pi*p)) :=
    ((by fun_prop : Continuous (fun p:ℝ=>P.eval (p^2))).div (by fun_prop)
      (fun p=>pow_ne_zero _ (hd p).ne')).div (by fun_prop) (fun p=>(Real.cosh_pos _).ne')
  apply (((polynomial_sech_integrable P Real.pi_pos).norm).div_const ((Y^2)^k)).mono' hm.aestronglyMeasurable
  filter_upwards with p
  simp only [Real.norm_eq_abs,abs_div,abs_of_pos (Real.cosh_pos _),abs_of_pos (pow_pos (hd p) k)]
  have hh : (Y^2)^k ≤ (p^2+Y^2)^k := pow_le_pow_left₀ (by positivity) (by nlinarith) k
  calc
    _ = |P.eval (p^2)|/Real.cosh (Real.pi*p)/(p^2+Y^2)^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hh
noncomputable def rationalSechMoment (Y : ℝ) (k : ℕ) (P : Polynomial ℝ) : ℝ :=
  2*∫ p in Set.Ioi (0:ℝ),P.eval (p^2)/(p^2+Y^2)^k/Real.cosh (Real.pi*p)
lemma rationalSechMoment_add {Y : ℝ} (hY : 0 < Y) (k : ℕ) (P Q : Polynomial ℝ) :
    rationalSechMoment Y k (P+Q)=rationalSechMoment Y k P+rationalSechMoment Y k Q := by
  simp only [rationalSechMoment,eval_add,add_div]
  rw [integral_add (rational_sech_integrable hY k P) (rational_sech_integrable hY k Q)]
  ring
lemma rationalSechMoment_smul (Y a : ℝ) (k : ℕ) (P : Polynomial ℝ) :
    rationalSechMoment Y k (a • P)=a*rationalSechMoment Y k P := by
  simp only [rationalSechMoment,eval_smul,smul_eq_mul,mul_div_assoc]
  rw [integral_const_mul]
  ring
lemma rationalSechMoment_neg (Y : ℝ) (k : ℕ) (P : Polynomial ℝ) :
    rationalSechMoment Y k (-P) = -rationalSechMoment Y k P := by
  simpa using rationalSechMoment_smul Y (-1) k P
lemma rationalSechMoment_sub {Y : ℝ} (hY : 0 < Y) (k : ℕ) (P Q : Polynomial ℝ) :
    rationalSechMoment Y k (P-Q)=rationalSechMoment Y k P-rationalSechMoment Y k Q := by
  rw [sub_eq_add_neg,rationalSechMoment_add hY,rationalSechMoment_neg,sub_eq_add_neg]
lemma rationalSechMoment_sum {Y : ℝ} (hY : 0 < Y) (k : ℕ) {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial ℝ) :
    rationalSechMoment Y k (∑ i∈s,P i)=∑ i∈s,rationalSechMoment Y k (P i) := by
  simp only [rationalSechMoment,eval_finsetSum,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ => rational_sech_integrable hY k (P i)),Finset.mul_sum]
lemma rationalSechMoment_den {Y : ℝ} (hY : 0 < Y) (k : ℕ) (P : Polynomial ℝ) :
    rationalSechMoment Y (k+1) ((X+Polynomial.C (Y^2))*P)=rationalSechMoment Y k P := by
  unfold rationalSechMoment
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  have hd : p^2+Y^2 ≠ 0 := (show 0 < p^2+Y^2 by positivity).ne'
  simp only [eval_mul,eval_add,eval_X,eval_C,pow_succ]
  field_simp
lemma rationalSechMoment_sq_nonneg (Y : ℝ) (k : ℕ) (P : Polynomial ℝ) :
    0 ≤ rationalSechMoment Y k (P^2) := by
  unfold rationalSechMoment
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro p
  simp only [eval_pow]
  positivity
lemma rationalSechMoment_zero_mul (Y : ℝ) (P Q : Polynomial ℝ) :
    rationalSechMoment Y 0 (P*Q)=polynomialSechInner P Q := by
  simp only [rationalSechMoment,pow_zero,div_one,eval_mul,polynomialSechInner_eq]
lemma rationalSechMoment_residual {Y : ℝ} (hY : 0 < Y) (P : Polynomial ℝ) :
    rationalSechMoment Y 2 ((1-(X+Polynomial.C (Y^2))*P)^2)=
      rationalSechMoment Y 2 1-2*rationalSechMoment Y 1 P+polynomialSechInner P P := by
  have he : (1-(X+Polynomial.C (Y^2))*P)^2=
      1-(2:ℝ) • ((X+Polynomial.C (Y^2))*P)+(X+Polynomial.C (Y^2))*((X+Polynomial.C (Y^2))*(P*P)) := by
    simp only [Algebra.smul_def,map_ofNat]
    ring
  rw [he,rationalSechMoment_add hY,rationalSechMoment_sub hY,rationalSechMoment_smul,
    rationalSechMoment_den hY 1,rationalSechMoment_den hY 1,
    rationalSechMoment_den hY 0,rationalSechMoment_zero_mul]
noncomputable def resolventCoeff (Y : ℝ) (n : ℕ) : ℝ :=
  rationalSechMoment Y 1 (evenPoly (-1) n)
lemma resolventCoeff_bessel {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    ∑ j:Fin (n+1),resolventCoeff Y j^2 ≤ rationalSechMoment Y 2 1 := by
  let a : Fin (n+1) → ℝ := fun j=>resolventCoeff Y j
  have h:=rationalSechMoment_sq_nonneg Y 2 (1-(X+Polynomial.C (Y^2))*pollaczekCombination a)
  rw [rationalSechMoment_residual hY,pollaczekCombination_inner] at h
  have he : rationalSechMoment Y 1 (pollaczekCombination a)=∑ j:Fin (n+1),a j^2 := by
    rw [pollaczekCombination,rationalSechMoment_sum hY]
    simp only [rationalSechMoment_smul,a,resolventCoeff,pow_two]
  rw [he] at h
  change ∑ j,a j^2 ≤ _
  linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
/-! Bessel bounds and the discrete Wronskian identify the decaying resolvent solution. -/
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Filter Topology
lemma square_prefix_monotone (a : ℕ → ℝ) : Monotone (fun n=>∑ j∈range n,a j^2) := by
  intro n m hnm
  apply sum_le_sum_of_subset_of_nonneg (range_mono hnm)
  intro j _ _
  positivity
lemma antitone_ratio_nonneg {a b : ℕ → ℝ} {K : ℝ}
    (ha : ∀ n,0 < a n) (hr : Antitone (fun n=>b n/a n))
    (hK : ∀ n,∑ j∈range n,b j^2 ≤ K)
    (hdiv : Tendsto (fun n=>∑ j∈range n,a j^2) atTop atTop) :
    ∀ n,0 ≤ b n/a n := by
  intro n
  by_contra hn
  have hn : b n/a n < 0 := lt_of_not_ge hn
  let r := b n/a n
  have hr0 : 0 < r^2 := sq_pos_of_neg hn
  obtain ⟨N,hN,hgt⟩ := ((eventually_ge_atTop n).and (hdiv.eventually
    (eventually_gt_atTop ((∑ j∈range n,a j^2)+K/r^2)))).exists
  have hs : r^2*(∑ j∈Ico n N,a j^2) ≤ ∑ j∈Ico n N,b j^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hbr : b j ≤ r*a j := (div_le_iff₀ (ha j)).1 (hr (mem_Ico.mp hj).1)
    have hneg : r*a j < 0 := mul_neg_of_neg_of_pos hn (ha j)
    have hbneg : b j ≤ 0 := by linarith
    have hh := mul_self_le_mul_self (by linarith : 0 ≤ -(r*a j)) (by linarith : -(r*a j) ≤ -b j)
    nlinarith
  have hb : (∑ j∈Ico n N,b j^2) ≤ K := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (by intro j hj;exact mem_range.2 (mem_Ico.mp hj).2)
      (fun j _ _ => sq_nonneg _)) (hK N)
  rw [sum_Ico_eq_sub _ hN] at hs
  have hgt' : K < (∑ j∈range N,a j^2 - ∑ j∈range n,a j^2)*r^2 := by
    apply (div_lt_iff₀ hr0).1
    linarith
  nlinarith
lemma antitone_ratio_zero {a b : ℕ → ℝ} {K : ℝ}
    (ha : ∀ n,0 < a n) (hr : Antitone (fun n=>b n/a n))
    (hK : ∀ n,∑ j∈range n,b j^2 ≤ K)
    (hdiv : Tendsto (fun n=>∑ j∈range n,a j^2) atTop atTop) :
    Tendsto (fun n=>b n/a n) atTop (𝓝 0) := by
  have hnn := antitone_ratio_nonneg ha hr hK hdiv
  have hK0 : 0 ≤ K := by simpa using hK 0
  have hs (n : ℕ) : (b n/a n)^2*(∑ j∈range (n+1),a j^2) ≤ K := by
    apply le_trans _ (hK (n+1))
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    have hbr : b n/a n*a j ≤ b j := (le_div_iff₀ (ha j)).1 (hr hjn)
    have hpos : 0 ≤ b n/a n*a j := mul_nonneg (hnn n) (ha j).le
    have hh := mul_self_le_mul_self hpos hbr
    nlinarith
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n=>lt_of_lt_of_le hl (hnn n))
  · intro u hu
    have hu2 : 0 < u^2 := sq_pos_of_pos hu
    filter_upwards [hdiv.eventually (eventually_gt_atTop (K/u^2))] with n hn
    have hmono := square_prefix_monotone a (Nat.le_succ n)
    have hn' : K < u^2*(∑ j∈range (n+1),a j^2) := by
      have hh := (div_lt_iff₀ hu2).1 (lt_of_lt_of_le hn hmono)
      nlinarith
    have hsum : 0 ≤ ∑ j∈range (n+1),a j^2 := sum_nonneg (fun j _ => sq_nonneg _)
    by_contra hnot
    have hb : u ≤ b n/a n := le_of_not_gt hnot
    have hsq : u^2 ≤ (b n/a n)^2 := by nlinarith [sq_nonneg (b n/a n-u)]
    have hh := mul_le_mul_of_nonneg_right hsq hsum
    linarith [hs n]
lemma wronskian_ratio_step {a b A : ℕ → ℝ} (ha : ∀ n,0 < a n) (hA : ∀ n,0 < A n)
    (hw : ∀ n,A n*(a (n+1)*b n-a n*b (n+1))=1) (n : ℕ) :
    b n/a n-b (n+1)/a (n+1)=1/(A n*a n*a (n+1)) := by
  have h0:=ha n
  have h1:=ha (n+1)
  have h2:=hA n
  apply (eq_div_iff (by positivity : A n*a n*a (n+1) ≠ 0)).2
  field_simp
  nlinarith [hw n]
lemma wronskian_ratio_antitone {a b A : ℕ → ℝ} (ha : ∀ n,0 < a n) (hA : ∀ n,0 < A n)
    (hw : ∀ n,A n*(a (n+1)*b n-a n*b (n+1))=1) :
    Antitone (fun n=>b n/a n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := wronskian_ratio_step ha hA hw n
  have hp : 0 < 1/(A n*a n*a (n+1)) := one_div_pos.2 (mul_pos (mul_pos (hA n) (ha n)) (ha (n+1)))
  linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real Finset Filter Topology
lemma rationalSechMoment_X {Y : ℝ} (hY : 0 < Y) (P : Polynomial ℝ) :
    rationalSechMoment Y 1 (X*P)+Y^2*rationalSechMoment Y 1 P=rationalSechMoment Y 0 P := by
  have h := rationalSechMoment_den hY 0 P
  have he : (X+Polynomial.C (Y^2))*P=X*P+Y^2 • P := by simp [add_mul,smul_eq_C_mul]
  rw [he,rationalSechMoment_add hY,rationalSechMoment_smul] at h
  exact h
lemma rationalSechMoment_basis_zero (Y : ℝ) (n : ℕ) :
    rationalSechMoment Y 0 (evenPoly (-1) n)=if n=0 then 1 else 0 := by
  have h:=rationalSechMoment_zero_mul Y (evenPoly (-1) n) (evenPoly (-1) 0)
  rw [polynomialSechInner_orthogonal] at h
  simpa only [evenPoly_zero,mul_one] using h
lemma resolventCoeff_jacobi_zero {Y : ℝ} (hY : 0 < Y) :
    jacobiA 0*resolventCoeff Y 1+(jacobiB 0+Y^2)*resolventCoeff Y 0=1 := by
  have h:=rationalSechMoment_X hY (evenPoly (-1) 0)
  rw [jacobi_poly_zero,rationalSechMoment_add hY,rationalSechMoment_smul,
    rationalSechMoment_smul,rationalSechMoment_basis_zero] at h
  simp only [ite_true,evenPoly_zero] at h
  dsimp [resolventCoeff]
  linarith
lemma resolventCoeff_jacobi_succ {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    jacobiA (n+1)*resolventCoeff Y (n+2)+(jacobiB (n+1)+Y^2)*resolventCoeff Y (n+1)+
      jacobiA n*resolventCoeff Y n=0 := by
  have h:=rationalSechMoment_X hY (evenPoly (-1) (n+1))
  rw [jacobi_poly_succ,rationalSechMoment_add hY,rationalSechMoment_add hY,
    rationalSechMoment_smul,rationalSechMoment_smul,rationalSechMoment_smul,
    rationalSechMoment_basis_zero] at h
  simp only [Nat.add_one_ne_zero,ite_false] at h
  dsimp [resolventCoeff]
  linarith
noncomputable def signedResolventCoeff (Y : ℝ) (n : ℕ) : ℝ := (-1)^n*resolventCoeff Y n
lemma signedResolventCoeff_jacobi_zero {Y : ℝ} (hY : 0 < Y) :
    jacobiA 0*signedResolventCoeff Y 1=(Y^2+jacobiB 0)*signedResolventCoeff Y 0-1 := by
  have h:=resolventCoeff_jacobi_zero hY
  simp only [signedResolventCoeff,pow_zero,pow_one,one_mul,neg_mul,one_mul]
  linarith
lemma signedResolventCoeff_jacobi_succ {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    jacobiA (n+1)*signedResolventCoeff Y (n+2)=(Y^2+jacobiB (n+1))*signedResolventCoeff Y (n+1)-
      jacobiA n*signedResolventCoeff Y n := by
  have h:=resolventCoeff_jacobi_succ hY n
  simp only [signedResolventCoeff,pow_add,pow_one,neg_one_sq,mul_one,mul_neg,neg_mul]
  linear_combination ((-1:ℝ)^n)*h
lemma resolvent_wronskian {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    jacobiA n*(negativeEval Y (n+1)*signedResolventCoeff Y n-
      negativeEval Y n*signedResolventCoeff Y (n+1))=1 := by
  induction n with
  | zero =>
    have ha:=negativeEval_jacobi_zero Y
    have hb:=signedResolventCoeff_jacobi_zero hY
    simp only [negativeEval_zero] at ha ⊢
    linear_combination signedResolventCoeff Y 0*ha-hb
  | succ n ih =>
    have ha:=negativeEval_jacobi_succ Y n
    have hb:=signedResolventCoeff_jacobi_succ hY n
    linear_combination signedResolventCoeff Y (n+1)*ha-negativeEval Y (n+1)*hb+ih
lemma signedResolventCoeff_sq (Y : ℝ) (n : ℕ) :
    signedResolventCoeff Y n^2=resolventCoeff Y n^2 := by
  rw [signedResolventCoeff,mul_pow,←pow_mul,show n*2=2*n by omega,pow_mul]
  norm_num
lemma signedResolventCoeff_bessel {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    ∑ j∈range n,signedResolventCoeff Y j^2 ≤ rationalSechMoment Y 2 1 := by
  cases n with
  | zero =>
    simpa only [sum_range_zero,one_pow] using rationalSechMoment_sq_nonneg Y 2 (1:Polynomial ℝ)
  | succ n =>
    simpa only [signedResolventCoeff_sq,←Fin.sum_univ_eq_sum_range] using resolventCoeff_bessel hY n
lemma negativeEval_square_diverges {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun n=>∑ j∈range n,negativeEval Y j^2) atTop atTop := by
  obtain ⟨c,C,hc,hC,h⟩:=evenCoefficientKernel_bounds hY
  have ht : Tendsto (fun n:ℕ=>c*((n:ℝ)+1)^(2*Y)) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by positivity)).comp
      (tendsto_atTop_mono (fun n:ℕ=>(show (n:ℝ) ≤ (n:ℝ)+1 by linarith)) tendsto_natCast_atTop_atTop))
  have hu : Tendsto (evenCoefficientKernel Y) atTop atTop := tendsto_atTop_mono' atTop
    (h.mono (fun n hn=>hn.1)) ht
  apply (tendsto_add_atTop_iff_nat 1).1
  exact hu
lemma signedResolventCoeff_ratio_zero {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun n=>signedResolventCoeff Y n/negativeEval Y n) atTop (𝓝 0) := by
  apply antitone_ratio_zero (negativeEval_pos hY)
    (wronskian_ratio_antitone (negativeEval_pos hY) jacobiA_pos (resolvent_wronskian hY))
    (signedResolventCoeff_bessel hY) (negativeEval_square_diverges hY)
lemma signedResolventCoeff_pos {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    0 < signedResolventCoeff Y n := by
  have hn:=antitone_ratio_nonneg (negativeEval_pos hY)
    (wronskian_ratio_antitone (negativeEval_pos hY) jacobiA_pos (resolvent_wronskian hY))
    (signedResolventCoeff_bessel hY) (negativeEval_square_diverges hY) (n+1)
  have hs:=wronskian_ratio_step (negativeEval_pos hY) jacobiA_pos (resolvent_wronskian hY) n
  have hp : 0 < 1/(jacobiA n*negativeEval Y n*negativeEval Y (n+1)) :=
    one_div_pos.2 (mul_pos (mul_pos (jacobiA_pos n) (negativeEval_pos hY n)) (negativeEval_pos hY (n+1)))
  have hh : 0 < signedResolventCoeff Y n/negativeEval Y n := by linarith
  exact (div_pos_iff_of_pos_right (negativeEval_pos hY n)).1 hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
lemma poch_ratio_factor_tendsto (a : ℝ) :
    Tendsto (fun n:ℕ=>(a+n)/(n+1)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n:ℕ=>(show (n:ℝ) ≤ (n:ℝ)+1 by linarith)) tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds.div_atTop ht (a:=a-1)).add_const 1
  simpa only [zero_add] using hh.congr (fun n=>by change (a-1)/((n:ℝ)+1)+1=(a+n)/(n+1);field_simp;ring)
lemma pochRatio_same_normalized_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n:ℕ=>pochRatio a n/((n:ℝ)+1)^(a-1)) atTop (𝓝 (1/Gamma a)) := by
  have hh:=(pochRatio_normalized_tendsto ha).div (poch_ratio_factor_tendsto a) one_ne_zero
  simp only [div_one] at hh
  apply hh.congr
  intro n
  change (pochRatio a (n+1)/((n:ℝ)+1)^(a-1))/((a+n)/(n+1)) = _
  rw [pochRatio_succ]
  have hf : (a+(n:ℝ))/(n+1) ≠ 0 := by positivity
  field_simp
lemma pochRatio_power_bounds {a : ℝ} (ha : 0 < a) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(a-1) ≤ pochRatio a n ∧ pochRatio a n ≤ C*((n:ℝ)+1)^(a-1) := by
  obtain ⟨c,C,hc,hC,h⟩:=positive_sequence_global_bounds
    (fun n=>div_pos (pochRatio_pos ha n) (Real.rpow_pos_of_pos (by positivity) _))
    (by positivity : 0 < 1/Gamma a) (pochRatio_same_normalized_tendsto ha)
  refine ⟨c,C,hc,hC,fun n=>?_⟩
  exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).1,
    (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).2⟩
noncomputable def reciprocalPoch (r : ℝ) (n : ℕ) : ℝ := (pochRatio (r+1) n)⁻¹
lemma reciprocalPoch_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < reciprocalPoch r n :=
  inv_pos.2 (pochRatio_pos (by positivity) n)
lemma reciprocalPoch_step {r : ℝ} (hr : 0 < r) (n : ℕ) :
    reciprocalPoch r n-reciprocalPoch r (n+1)=r/(r+n+1)*reciprocalPoch r n := by
  unfold reciprocalPoch
  rw [pochRatio_succ]
  have h0 : pochRatio (r+1) n ≠ 0 := (pochRatio_pos (by positivity) n).ne'
  have h1 : r+(n:ℝ)+1 ≠ 0 := by positivity
  have h2 : r+1+(n:ℝ) ≠ 0 := by positivity
  have h3 : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring
lemma reciprocalPoch_normalized_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n:ℕ=>reciprocalPoch r n/((n:ℝ)+1)^(-r)) atTop (𝓝 ((1/Gamma (r+1))⁻¹)) := by
  have hh := (pochRatio_same_normalized_tendsto (by positivity : 0 < r+1)).inv₀ (by positivity)
  apply hh.congr
  intro n
  simp only [add_sub_cancel_right,reciprocalPoch,inv_div]
  rw [Real.rpow_neg (by positivity)]
  field_simp
lemma reciprocalPoch_bounds {r : ℝ} (hr : 0 < r) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(-r) ≤ reciprocalPoch r n ∧ reciprocalPoch r n ≤ C*((n:ℝ)+1)^(-r) := by
  obtain ⟨c,C,hc,hC,h⟩:=positive_sequence_global_bounds
    (fun n=>div_pos (reciprocalPoch_pos hr n) (Real.rpow_pos_of_pos (by positivity) _))
    (by positivity : 0 < (1/Gamma (r+1))⁻¹) (reciprocalPoch_normalized_tendsto hr)
  refine ⟨c,C,hc,hC,fun n=>?_⟩
  exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).1,
    (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).2⟩
lemma reciprocalPoch_zero {r : ℝ} (hr : 0 < r) : Tendsto (reciprocalPoch r) atTop (𝓝 0) := by
  have ht : Tendsto (fun n:ℕ=>((n:ℝ)+1)^(-r)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hr).comp (tendsto_atTop_mono (fun n:ℕ=>(show (n:ℝ) ≤ (n:ℝ)+1 by linarith)) tendsto_natCast_atTop_atTop)
  have hh := (reciprocalPoch_normalized_tendsto hr).mul ht
  simp only [mul_zero] at hh
  apply hh.congr
  intro n
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (by positivity) _).ne'
lemma reciprocalPoch_difference_bounds {r : ℝ} (hr : 0 < r) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(-r-1) ≤ reciprocalPoch r n-reciprocalPoch r (n+1) ∧
      reciprocalPoch r n-reciprocalPoch r (n+1) ≤ C*((n:ℝ)+1)^(-r-1) := by
  obtain ⟨c,C,hc,hC,h⟩:=reciprocalPoch_bounds hr
  refine ⟨r*c/(r+1),r*C,by positivity,by positivity,fun n=>?_⟩
  rw [reciprocalPoch_step hr,Real.rpow_sub_one (by positivity)]
  have hratio : r/((r+1)*((n:ℝ)+1)) ≤ r/(r+n+1) ∧ r/(r+n+1) ≤ r/((n:ℝ)+1) := by
    constructor <;> apply div_le_div_of_nonneg_left hr.le (by positivity) <;>
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  constructor
  · have hh:=mul_le_mul hratio.1 (h n).1 (by positivity) (by positivity)
    convert hh using 1; first | rfl | field_simp
  · have hh:=mul_le_mul hratio.2 (h n).2 (reciprocalPoch_pos hr n).le (by positivity)
    convert hh using 1; first | rfl | field_simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Filter Topology
lemma difference_comparison {r t : ℕ → ℝ} {c C : ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (hd : ∀ n,c*(t n-t (n+1)) ≤ r n-r (n+1) ∧ r n-r (n+1) ≤ C*(t n-t (n+1))) :
    ∀ n,c*t n ≤ r n ∧ r n ≤ C*t n := by
  have hl : Antitone (fun n=>r n-c*t n) := by
    apply antitone_nat_of_succ_le
    intro n
    linarith [(hd n).1]
  have hu : Antitone (fun n=>C*t n-r n) := by
    apply antitone_nat_of_succ_le
    intro n
    linarith [(hd n).2]
  have hlt : Tendsto (fun n=>r n-c*t n) atTop (𝓝 0) := by simpa using hr.sub (ht.const_mul c)
  have hut : Tendsto (fun n=>C*t n-r n) atTop (𝓝 0) := by simpa using (ht.const_mul C).sub hr
  intro n
  have hlo := hl.le_of_tendsto hlt n
  have hup := hu.le_of_tendsto hut n
  constructor <;> linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
lemma negativeEval_power_bounds {s : ℝ} (hs : 0 < s) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(s-1/2) ≤ negativeEval s n ∧
      negativeEval s n ≤ C*((n:ℝ)+1)^(s-1/2) := by
  obtain ⟨c,C,hc,hC,h⟩:=pochRatio_power_bounds (by positivity : 0 < s+1/2)
  refine ⟨min 1 (2*s)*c,(max 1 (2*s)*exp (2*(2*s-1)^2))*C,by positivity,by positivity,fun n=>?_⟩
  have hp:=meixner_even_product_bounds hs n
  rw [baseProduct_eq_poch] at hp
  have he : s+1/2-1=s-1/2 := by ring
  rw [he] at h
  constructor
  · apply le_trans _ hp.1
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (h n).1 (by positivity : 0 ≤ min 1 (2*s))
  · exact hp.2.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (h n).2 (show 0 ≤ max 1 (2*s)*exp (2*(2*s-1)^2) by positivity))
lemma nat_power_shift_bounds (r : ℝ) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^r ≤ ((n:ℝ)+2)^r ∧ ((n:ℝ)+2)^r ≤ C*((n:ℝ)+1)^r := by
  have ht : Tendsto (fun n:ℕ=>((n:ℝ)+2)^r/((n:ℝ)+1)^r) atTop (𝓝 1) := by
    have hh := (poch_ratio_factor_tendsto 2).rpow_const (p:=r) (by simp)
    simp only [Real.one_rpow] at hh
    apply hh.congr
    intro n
    rw [Real.div_rpow (by positivity) (by positivity)]
    simp [add_comm]
  obtain ⟨c,C,hc,hC,h⟩:=positive_sequence_global_bounds (fun n=>div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)) zero_lt_one ht
  exact ⟨c,C,hc,hC,fun n=>⟨(le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).1,(div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 (h n).2⟩⟩
lemma jacobiA_power_bounds (n : ℕ) :
    (1/2:ℝ)*((n:ℝ)+1)^2 ≤ jacobiA n ∧ jacobiA n ≤ ((n:ℝ)+1)^2 := by
  unfold jacobiA
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) n]
lemma resolvent_denominator_bounds {Y : ℝ} (hY : 0 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(2*Y+1) ≤ jacobiA n*negativeEval Y n*negativeEval Y (n+1) ∧
      jacobiA n*negativeEval Y n*negativeEval Y (n+1) ≤ C*((n:ℝ)+1)^(2*Y+1) := by
  obtain ⟨c,C,hc,hC,h⟩:=negativeEval_power_bounds hY
  obtain ⟨d,D,hd,hD,hs⟩:=nat_power_shift_bounds (Y-1/2)
  refine ⟨(1/2)*c*c*d,C*C*D,by positivity,by positivity,fun n=>?_⟩
  have hlo : c*d*((n:ℝ)+1)^(Y-1/2) ≤ negativeEval Y (n+1) := by
    have hh:=mul_le_mul_of_nonneg_left (hs n).1 hc.le
    have he : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [he] at hh
    apply le_trans _ (h (n+1)).1
    simpa [mul_assoc] using hh
  have hhi : negativeEval Y (n+1) ≤ C*D*((n:ℝ)+1)^(Y-1/2) := by
    have hh:=mul_le_mul_of_nonneg_left (hs n).2 hC.le
    have he : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [he] at hh
    exact (h (n+1)).2.trans (by simpa [mul_assoc] using hh)
  have he : ((n:ℝ)+1)^2*((n:ℝ)+1)^(Y-1/2)*((n:ℝ)+1)^(Y-1/2)=((n:ℝ)+1)^(2*Y+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_add (by positivity),←Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  constructor
  · have hh:=mul_le_mul (mul_le_mul (jacobiA_power_bounds n).1 (h n).1 (by positivity) (jacobiA_pos n).le) hlo (by positivity) (mul_pos (jacobiA_pos n) (negativeEval_pos hY n)).le
    convert hh using 1; first | rfl | (rw [←he]; ring)
  · have hh:=mul_le_mul (mul_le_mul (jacobiA_power_bounds n).2 (h n).2 (negativeEval_pos hY n).le (by positivity)) hhi (negativeEval_pos hY (n+1)).le (by positivity)
    convert hh using 1; first | rfl | (rw [←he]; ring)
lemma resolvent_ratio_difference_bounds {Y : ℝ} (hY : 0 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(-2*Y-1) ≤ signedResolventCoeff Y n/negativeEval Y n-signedResolventCoeff Y (n+1)/negativeEval Y (n+1) ∧
      signedResolventCoeff Y n/negativeEval Y n-signedResolventCoeff Y (n+1)/negativeEval Y (n+1) ≤ C*((n:ℝ)+1)^(-2*Y-1) := by
  obtain ⟨c,C,hc,hC,h⟩:=resolvent_denominator_bounds hY
  refine ⟨C⁻¹,c⁻¹,by positivity,by positivity,fun n=>?_⟩
  rw [wronskian_ratio_step (negativeEval_pos hY) jacobiA_pos (resolvent_wronskian hY)]
  have he : ((n:ℝ)+1)^(-2*Y-1)=(((n:ℝ)+1)^(2*Y+1))⁻¹ := by
    rw [show -2*Y-1=-(2*Y+1) by ring,Real.rpow_neg (by positivity)]
  rw [he,←mul_inv,←mul_inv,one_div]
  have hp : 0 < jacobiA n*negativeEval Y n*negativeEval Y (n+1) := mul_pos (mul_pos (jacobiA_pos n) (negativeEval_pos hY n)) (negativeEval_pos hY (n+1))
  exact ⟨(inv_le_inv₀ (by positivity) hp).2 (h n).2,(inv_le_inv₀ hp (by positivity)).2 (h n).1⟩
lemma resolvent_ratio_power_bounds {Y : ℝ} (hY : 0 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(-2*Y) ≤ signedResolventCoeff Y n/negativeEval Y n ∧
      signedResolventCoeff Y n/negativeEval Y n ≤ C*((n:ℝ)+1)^(-2*Y) := by
  obtain ⟨a,A,ha,hA,h⟩:=resolvent_ratio_difference_bounds hY
  obtain ⟨b,B,hb,hB,hd⟩:=reciprocalPoch_difference_bounds (show 0 < 2*Y by positivity)
  obtain ⟨c,C,hc,hC,ht⟩:=reciprocalPoch_bounds (show 0 < 2*Y by positivity)
  have hh:=difference_comparison (signedResolventCoeff_ratio_zero hY) (reciprocalPoch_zero (show 0 < 2*Y by positivity)) (c:=a/B) (C:=A/b) (fun n=>by
    have he : -(2*Y)-1=-2*Y-1 := by ring
    rw [he] at hd
    constructor
    · have hp:=mul_le_mul_of_nonneg_left (hd n).2 (show 0 ≤ a/B by positivity)
      have heq : a/B*(B*((n:ℝ)+1)^(-2*Y-1))=a*((n:ℝ)+1)^(-2*Y-1) := by field_simp
      rw [heq] at hp
      exact hp.trans (h n).1
    · have hp:=mul_le_mul_of_nonneg_left (hd n).1 (show 0 ≤ A/b by positivity)
      have heq : A/b*(b*((n:ℝ)+1)^(-2*Y-1))=A*((n:ℝ)+1)^(-2*Y-1) := by field_simp
      rw [heq] at hp
      exact (h n).2.trans hp)
  refine ⟨a/B*c,A/b*C,by positivity,by positivity,fun n=>?_⟩
  have he : -(2*Y)=-2*Y := by ring
  rw [he] at ht
  constructor
  · apply le_trans _ (hh n).1
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (ht n).1 (show 0 ≤ a/B by positivity)
  · exact (hh n).2.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (ht n).2 (show 0 ≤ A/b by positivity))
lemma signedResolventCoeff_power_bounds {Y : ℝ} (hY : 0 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(-Y-1/2) ≤ signedResolventCoeff Y n ∧
      signedResolventCoeff Y n ≤ C*((n:ℝ)+1)^(-Y-1/2) := by
  obtain ⟨a,A,ha,hA,h⟩:=negativeEval_power_bounds hY
  obtain ⟨b,B,hb,hB,hd⟩:=resolvent_ratio_power_bounds hY
  refine ⟨a*b,A*B,by positivity,by positivity,fun n=>?_⟩
  have he : ((n:ℝ)+1)^(Y-1/2)*((n:ℝ)+1)^(-2*Y)=((n:ℝ)+1)^(-Y-1/2) := by
    rw [←Real.rpow_add (by positivity)]
    congr 1
    ring
  have heq : negativeEval Y n*(signedResolventCoeff Y n/negativeEval Y n)=signedResolventCoeff Y n := mul_div_cancel₀ _ (negativeEval_pos hY n).ne'
  constructor
  · have hh:=mul_le_mul (h n).1 (hd n).1 (by positivity) (negativeEval_pos hY n).le
    rw [heq] at hh
    convert hh using 1; first | rfl | (rw [←he]; ring)
  · have hh:=mul_le_mul (h n).2 (hd n).2 (div_pos (signedResolventCoeff_pos hY n) (negativeEval_pos hY n)).le (by positivity)
    rw [heq] at hh
    convert hh using 1; first | rfl | (rw [←he]; ring)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Real Filter Topology
noncomputable def mixedWronskian (v Y : ℝ) (n : ℕ) : ℝ :=
  jacobiA n*(negativeEval v (n+1)*signedResolventCoeff Y n-negativeEval v n*signedResolventCoeff Y (n+1))
lemma mixedWronskian_sum {Y : ℝ} (hY : 0 < Y) (v : ℝ) (n : ℕ) :
    mixedWronskian v Y n=1-(Y^2-v^2)*(∑ j∈range (n+1),negativeEval v j*signedResolventCoeff Y j) := by
  induction n with
  | zero =>
    have ha:=negativeEval_jacobi_zero v
    have hd:=signedResolventCoeff_jacobi_zero hY
    simp only [mixedWronskian,sum_range_succ,sum_range_zero,zero_add,negativeEval_zero,one_mul] at *
    linear_combination signedResolventCoeff Y 0*ha-hd
  | succ n ih =>
    have ha:=negativeEval_jacobi_succ v n
    have hd:=signedResolventCoeff_jacobi_succ hY n
    rw [sum_range_succ]
    dsimp [mixedWronskian] at ih ⊢
    linear_combination signedResolventCoeff Y (n+1)*ha-negativeEval v (n+1)*hd+ih
lemma mixedWronskian_power_bound {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) :
    ∃ C : ℝ,0 < C ∧ ∀ n:ℕ,|mixedWronskian v Y n| ≤ C*((n:ℝ)+1)^(v-Y+1) := by
  obtain ⟨a,A,ha,hA,h⟩:=negativeEval_power_bounds hv
  obtain ⟨b,B,hb,hB,hd⟩:=signedResolventCoeff_power_bounds hY
  obtain ⟨c,C,hc,hC,hvshift⟩:=nat_power_shift_bounds (v-1/2)
  obtain ⟨d,D,hdp,hD,hYshift⟩:=nat_power_shift_bounds (-Y-1/2)
  refine ⟨A*B*(C+D),by positivity,fun n=>?_⟩
  have ha' : negativeEval v (n+1) ≤ A*C*((n:ℝ)+1)^(v-1/2) := by
    have hh:=mul_le_mul_of_nonneg_left (hvshift n).2 hA.le
    have he : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [he] at hh
    exact (h (n+1)).2.trans (by simpa [mul_assoc] using hh)
  have hb' : signedResolventCoeff Y (n+1) ≤ B*D*((n:ℝ)+1)^(-Y-1/2) := by
    have hh:=mul_le_mul_of_nonneg_left (hYshift n).2 hB.le
    have he : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [he] at hh
    exact (hd (n+1)).2.trans (by simpa [mul_assoc] using hh)
  have hp := mul_le_mul ha' (hd n).2 (signedResolventCoeff_pos hY n).le (by positivity)
  have hq := mul_le_mul (h n).2 hb' (signedResolventCoeff_pos hY (n+1)).le (by positivity)
  have habs : |negativeEval v (n+1)*signedResolventCoeff Y n-negativeEval v n*signedResolventCoeff Y (n+1)| ≤
      A*C*((n:ℝ)+1)^(v-1/2)*(B*((n:ℝ)+1)^(-Y-1/2))+A*((n:ℝ)+1)^(v-1/2)*(B*D*((n:ℝ)+1)^(-Y-1/2)) := by
    apply le_trans (by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (negativeEval v (n+1)*signedResolventCoeff Y n) 0 (negativeEval v n*signedResolventCoeff Y (n+1))))
    rw [abs_of_pos (mul_pos (negativeEval_pos hv _) (signedResolventCoeff_pos hY _)),abs_of_pos (mul_pos (negativeEval_pos hv _) (signedResolventCoeff_pos hY _))]
    linarith
  have hh:=mul_le_mul (jacobiA_power_bounds n).2 habs (abs_nonneg _) (by positivity)
  rw [mixedWronskian,abs_mul,abs_of_pos (jacobiA_pos n)]
  apply hh.trans_eq
  have he : ((n:ℝ)+1)^2*((n:ℝ)+1)^(v-1/2)*((n:ℝ)+1)^(-Y-1/2)=((n:ℝ)+1)^(v-Y+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_add (by positivity),←Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  rw [←he]
  ring
lemma mixedWronskian_zero {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    Tendsto (mixedWronskian v Y) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩:=mixedWronskian_power_bound hY hv
  have ht : Tendsto (fun n:ℕ=>C*((n:ℝ)+1)^(v-Y+1)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (show 0 < Y-v-1 by linarith)).comp
      (tendsto_atTop_mono (fun n:ℕ=>(show (n:ℝ) ≤ (n:ℝ)+1 by linarith)) tendsto_natCast_atTop_atTop)).const_mul C
    simp only [mul_zero] at hh
    simpa only [Function.comp_apply,show -(Y-v-1)=v-Y+1 by ring] using hh
  exact squeeze_zero_norm (by simpa only [Real.norm_eq_abs] using h) ht
noncomputable def resolventEvalResidual (v Y : ℝ) (n : ℕ) : ℝ :=
  1/(Y^2-v^2)-(∑ j∈range n,negativeEval v j*signedResolventCoeff Y j)
lemma resolventEvalResidual_zero {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    Tendsto (resolventEvalResidual v Y) atTop (𝓝 0) := by
  have hden : Y^2-v^2 ≠ 0 := by nlinarith
  apply (tendsto_add_atTop_iff_nat 1).1
  have hh := (mixedWronskian_zero hY hv hgap).div_const (Y^2-v^2)
  simp only [zero_div] at hh
  apply hh.congr
  intro n
  dsimp [resolventEvalResidual]
  rw [mixedWronskian_sum hY]
  field_simp
lemma resolventEvalResidual_step (v Y : ℝ) (n : ℕ) :
    resolventEvalResidual v Y n-resolventEvalResidual v Y (n+1)=negativeEval v n*signedResolventCoeff Y n := by
  simp only [resolventEvalResidual,sum_range_succ]
  ring
lemma resolventEvalResidual_power_bounds {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n:ℕ,
      c*((n:ℝ)+1)^(v-Y) ≤ resolventEvalResidual v Y n ∧
      resolventEvalResidual v Y n ≤ C*((n:ℝ)+1)^(v-Y) := by
  obtain ⟨a,A,ha,hA,h⟩:=negativeEval_power_bounds hv
  obtain ⟨b,B,hb,hB,hd⟩:=signedResolventCoeff_power_bounds hY
  have hr : 0 < Y-v := by linarith
  obtain ⟨c,C,hc,hC,ht⟩:=reciprocalPoch_difference_bounds hr
  obtain ⟨d,D,hdp,hD,hu⟩:=reciprocalPoch_bounds hr
  have hprod (n : ℕ) : a*b*((n:ℝ)+1)^(v-Y-1) ≤ negativeEval v n*signedResolventCoeff Y n ∧
      negativeEval v n*signedResolventCoeff Y n ≤ A*B*((n:ℝ)+1)^(v-Y-1) := by
    have he : ((n:ℝ)+1)^(v-1/2)*((n:ℝ)+1)^(-Y-1/2)=((n:ℝ)+1)^(v-Y-1) := by
      rw [←Real.rpow_add (by positivity)]
      congr 1
      ring
    constructor
    · have hh:=mul_le_mul (h n).1 (hd n).1 (by positivity) (negativeEval_pos hv n).le
      convert hh using 1; first | rfl | (rw [←he];ring)
    · have hh:=mul_le_mul (h n).2 (hd n).2 (signedResolventCoeff_pos hY n).le (by positivity)
      convert hh using 1; first | rfl | (rw [←he];ring)
  have hh:=difference_comparison (resolventEvalResidual_zero hY hv hgap) (reciprocalPoch_zero hr) (c:=a*b/C) (C:=A*B/c) (fun n=>by
    rw [resolventEvalResidual_step]
    have he : -(Y-v)-1=v-Y-1 := by ring
    rw [he] at ht
    constructor
    · have hp:=mul_le_mul_of_nonneg_left (ht n).2 (show 0 ≤ a*b/C by positivity)
      have heq : a*b/C*(C*((n:ℝ)+1)^(v-Y-1))=a*b*((n:ℝ)+1)^(v-Y-1) := by field_simp
      rw [heq] at hp
      exact hp.trans (hprod n).1
    · have hp:=mul_le_mul_of_nonneg_left (ht n).1 (show 0 ≤ A*B/c by positivity)
      have heq : A*B/c*(c*((n:ℝ)+1)^(v-Y-1))=A*B*((n:ℝ)+1)^(v-Y-1) := by field_simp
      rw [heq] at hp
      exact (hprod n).2.trans hp)
  refine ⟨a*b/C*d,A*B/c*D,by positivity,by positivity,fun n=>?_⟩
  have he : -(Y-v)=v-Y := by ring
  rw [he] at hu
  constructor
  · apply le_trans _ (hh n).1
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hu n).1 (show 0 ≤ a*b/C by positivity)
  · exact (hh n).2.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hu n).2 (show 0 ≤ A*B/c by positivity))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Real Filter Topology
lemma difference_lower_of_nonneg {r t : ℕ → ℝ} {c : ℝ}
    (hr : ∀ n,0 ≤ r n) (ht : Tendsto t atTop (𝓝 0))
    (hd : ∀ n,c*(t n-t (n+1)) ≤ r n-r (n+1)) : ∀ n,c*t n ≤ r n := by
  have ha : Antitone (fun n=>r n-c*t n) := by
    apply antitone_nat_of_succ_le
    intro n
    linarith [hd n]
  intro n
  have he : ∀ᶠ m:ℕ in atTop,c*t n-c*t m ≤ r n := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have hh:=ha hm
    linarith [hr m]
  have hh : Tendsto (fun m=>c*t n-c*t m) atTop (𝓝 (c*t n)) := by
    simpa using tendsto_const_nhds.sub (ht.const_mul c)
  exact le_of_tendsto hh he
noncomputable def resolventNormResidual (Y : ℝ) (n : ℕ) : ℝ :=
  rationalSechMoment Y 2 1-∑ j∈range n,resolventCoeff Y j^2
lemma resolventNormResidual_nonneg {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    0 ≤ resolventNormResidual Y n := by
  have h:=signedResolventCoeff_bessel hY n
  simp only [signedResolventCoeff_sq] at h
  exact sub_nonneg.2 h
lemma resolventNormResidual_step (Y : ℝ) (n : ℕ) :
    resolventNormResidual Y n-resolventNormResidual Y (n+1)=signedResolventCoeff Y n^2 := by
  rw [signedResolventCoeff_sq]
  simp only [resolventNormResidual,sum_range_succ]
  ring
lemma resolventNormResidual_lower {Y : ℝ} (hY : 0 < Y) :
    ∃ c : ℝ,0 < c ∧ ∀ n:ℕ,c*((n:ℝ)+1)^(-2*Y) ≤ resolventNormResidual Y n := by
  obtain ⟨a,A,ha,hA,h⟩:=signedResolventCoeff_power_bounds hY
  obtain ⟨b,B,hb,hB,ht⟩:=reciprocalPoch_difference_bounds (show 0 < 2*Y by positivity)
  obtain ⟨c,C,hc,hC,hu⟩:=reciprocalPoch_bounds (show 0 < 2*Y by positivity)
  have hh:=difference_lower_of_nonneg (resolventNormResidual_nonneg hY) (reciprocalPoch_zero (show 0 < 2*Y by positivity)) (c:=a^2/B) (fun n=>by
    rw [resolventNormResidual_step]
    have hp:=mul_le_mul_of_nonneg_left (ht n).2 (show 0 ≤ a^2/B by positivity)
    have he : a^2/B*(B*((n:ℝ)+1)^(-(2*Y)-1))=(a*((n:ℝ)+1)^(-Y-1/2))^2 := by
      rw [mul_pow,←Real.rpow_natCast (((n:ℝ)+1)^(-Y-1/2)) 2,←Real.rpow_mul (by positivity)]
      simp only [Nat.cast_ofNat]
      have he : (-Y-1/2)*(2:ℝ)=-(2*Y)-1 := by ring
      rw [he]
      field_simp
    rw [he] at hp
    exact hp.trans (pow_le_pow_left₀ (by positivity) (h n).1 2))
  refine ⟨a^2/B*c,by positivity,fun n=>?_⟩
  have he : -(2*Y)=-2*Y := by ring
  rw [he] at hu
  apply le_trans _ (hh n)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hu n).1 (show 0 ≤ a^2/B by positivity)
lemma resolventNormResidual_pos {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    0 < resolventNormResidual Y n := by
  obtain ⟨c,hc,h⟩:=resolventNormResidual_lower hY
  exact lt_of_lt_of_le (by positivity) (h n)
lemma resolventEvalResidual_normalized_bound {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    ∃ C : ℝ,0 < C ∧ ∀ n:ℕ,resolventEvalResidual v Y n^2 ≤ C*((n:ℝ)+1)^(2*v)*resolventNormResidual Y n := by
  obtain ⟨a,A,ha,hA,h⟩:=resolventEvalResidual_power_bounds hY hv hgap
  obtain ⟨b,hb,hd⟩:=resolventNormResidual_lower hY
  refine ⟨A^2/b,by positivity,fun n=>?_⟩
  have hp : 0 ≤ resolventEvalResidual v Y n := le_trans (by positivity) (h n).1
  have hh:=pow_le_pow_left₀ hp (h n).2 2
  have he : (A*((n:ℝ)+1)^(v-Y))^2=(A^2/b)*((n:ℝ)+1)^(2*v)*(b*((n:ℝ)+1)^(-2*Y)) := by
    rw [mul_pow,←Real.rpow_natCast (((n:ℝ)+1)^(v-Y)) 2,←Real.rpow_mul (by positivity)]
    simp only [Nat.cast_ofNat]
    have he2 : ((n:ℝ)+1)^(2*v)*((n:ℝ)+1)^(-2*Y)=((n:ℝ)+1)^((v-Y)*2) := by
      rw [←Real.rpow_add (by positivity)]
      congr 1
      ring
    rw [←he2]
    field_simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hd n) (by positivity))
lemma rationalSechMoment_den_twice {Y : ℝ} (hY : 0 < Y) (P : Polynomial ℝ) :
    rationalSechMoment Y 2 ((X+Polynomial.C (Y^2))^2*P)=rationalSechMoment Y 0 P := by
  rw [show (X+Polynomial.C (Y^2))^2*P=(X+Polynomial.C (Y^2))*((X+Polynomial.C (Y^2))*P) by ring,
    rationalSechMoment_den hY 1,rationalSechMoment_den hY 0]
lemma rationalSechMoment_combination {Y : ℝ} (hY : 0 < Y) {n : ℕ} (a : Fin (n+1) → ℝ) (c : ℝ) :
    rationalSechMoment Y 2 (((X+Polynomial.C (Y^2))*pollaczekCombination a+Polynomial.C c)^2)=
      (∑ j:Fin (n+1),(a j+c*resolventCoeff Y j)^2)+c^2*resolventNormResidual Y (n+1) := by
  have he : ((X+Polynomial.C (Y^2))*pollaczekCombination a+Polynomial.C c)^2=
      (X+Polynomial.C (Y^2))^2*(pollaczekCombination a*pollaczekCombination a)+
      (2*c) • ((X+Polynomial.C (Y^2))*pollaczekCombination a)+c^2 • (1:Polynomial ℝ) := by
    simp only [smul_eq_C_mul,map_mul,map_pow,map_ofNat]
    ring
  rw [he,rationalSechMoment_add hY,rationalSechMoment_add hY,rationalSechMoment_smul,
    rationalSechMoment_smul,rationalSechMoment_den_twice hY,rationalSechMoment_den hY 1,
    rationalSechMoment_zero_mul,pollaczekCombination_inner]
  have hm : rationalSechMoment Y 1 (pollaczekCombination a)=∑ j:Fin (n+1),a j*resolventCoeff Y j := by
    rw [pollaczekCombination,rationalSechMoment_sum hY]
    simp only [rationalSechMoment_smul,resolventCoeff]
  rw [hm,resolventNormResidual,←Fin.sum_univ_eq_sum_range]
  have hs : (∑ j:Fin (n+1),(a j+c*resolventCoeff Y j)^2)=(∑ j:Fin (n+1),a j^2)+2*c*(∑ j:Fin (n+1),a j*resolventCoeff Y j)+c^2*(∑ j:Fin (n+1),resolventCoeff Y j^2) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring
lemma rational_combination_eval (Y v c : ℝ) (hden : Y^2-v^2 ≠ 0) {n : ℕ} (a : Fin (n+1) → ℝ) :
    (((X+Polynomial.C (Y^2))*pollaczekCombination a+Polynomial.C c).eval (-(v^2)))=
      (Y^2-v^2)*((pollaczekCombination (fun j=>a j+c*resolventCoeff Y j)).eval (-(v^2))+c*resolventEvalResidual v Y (n+1)) := by
  have he (j : ℕ) : resolventCoeff Y j*(evenPoly (-1) j).eval (-(v^2))=negativeEval v j*signedResolventCoeff Y j := by
    rw [evenPoly_negative_eval]
    dsimp [negativeEval,signedResolventCoeff]
    ring
  simp only [eval_add,eval_mul,eval_X,eval_C,pollaczekCombination_eval,add_mul,sum_add_distrib,mul_assoc,he,resolventEvalResidual,←Fin.sum_univ_eq_sum_range,←Finset.mul_sum]
  field_simp
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Real Filter Topology
lemma polynomial_linear_decomposition (Y : ℝ) (P : Polynomial ℝ) {n : ℕ} (hP : P.natDegree ≤ n) :
    ∃ a : Fin (n+1) → ℝ,∃ c : ℝ,P=(X+Polynomial.C (Y^2))*pollaczekCombination a+Polynomial.C c := by
  let q : Polynomial ℝ := X+Polynomial.C (Y^2)
  let Q : Polynomial ℝ := P /ₘ q
  have hQ : Q.natDegree ≤ n :=
    (Polynomial.natDegree_le_natDegree (degree_divByMonic_le P q)).trans hP
  obtain ⟨a,ha⟩:=polynomial_eq_pollaczek_sum Q hQ
  refine ⟨a,P.eval (-(Y^2)),?_⟩
  have hq : q=X-Polynomial.C (-(Y^2)) := by simp only [q,map_neg,sub_neg_eq_add]
  have hm : P %ₘ q=Polynomial.C (P.eval (-(Y^2))) := by
    rw [hq,modByMonic_X_sub_C_eq_C_eval]
  have hh : Polynomial.C (P.eval (-(Y^2)))+q*Q=P := by
    simpa only [Q,hm] using modByMonic_add_div P q
  change pollaczekCombination a=Q at ha
  rw [ha]
  exact hh.symm.trans (add_comm _ _)
lemma rational_polynomial_evaluation_bound {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n:ℕ in atTop,∀ P : Polynomial ℝ,P.natDegree ≤ n →
      P.eval (-(v^2))^2 ≤ C*((n:ℝ)+1)^(2*v)*rationalSechMoment Y 2 (P^2) := by
  obtain ⟨k,K,hk,hK,hkernel⟩:=polynomialChristoffel_bounds hv
  obtain ⟨E,hE,he⟩:=resolventEvalResidual_normalized_bound hY hv hgap
  obtain ⟨d,D,hd,hD,hshift⟩:=nat_power_shift_bounds (2*v)
  have hden : Y^2-v^2 ≠ 0 := by nlinarith
  let C0 := 2*(K+E*D)
  have hC0 : 0 < C0 := by dsimp [C0];positivity
  refine ⟨(Y^2-v^2)^2*C0,mul_pos (sq_pos_of_ne_zero hden) hC0,?_⟩
  filter_upwards [hkernel] with n hn
  intro P hP
  obtain ⟨a,c,rfl⟩:=polynomial_linear_decomposition Y P hP
  let z : Fin (n+1) → ℝ := fun j=>a j+c*resolventCoeff Y j
  let F := ∑ j:Fin (n+1),z j^2
  have hF : 0 ≤ F := sum_nonneg (fun j _=>sq_nonneg _)
  have hN : 0 ≤ resolventNormResidual Y (n+1) := resolventNormResidual_nonneg hY _
  have hkbound : (pollaczekCombination z).eval (-(v^2))^2 ≤ F*(K*((n:ℝ)+1)^(2*v)) := by
    have hh:=polynomial_evaluation_bound (pollaczekCombination z) (pollaczekCombination_degree z) (-(v^2))
    rw [pollaczekCombination_inner,←polynomialChristoffel_eq_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hn.2 hF)
  have hebound : resolventEvalResidual v Y (n+1)^2 ≤ E*D*((n:ℝ)+1)^(2*v)*resolventNormResidual Y (n+1) := by
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hshift n).2 hE.le) hN
    have hn2 : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [hn2] at hh
    exact (he (n+1)).trans (by simpa [mul_assoc] using hh)
  have hb : ((pollaczekCombination z).eval (-(v^2))+c*resolventEvalResidual v Y (n+1))^2 ≤
      C0*((n:ℝ)+1)^(2*v)*(F+c^2*resolventNormResidual Y (n+1)) := by
    have h1:=mul_le_mul_of_nonneg_left hebound (sq_nonneg c)
    have hs := sq_nonneg ((pollaczekCombination z).eval (-(v^2))-c*resolventEvalResidual v Y (n+1))
    have hk0 : 0 ≤ K*((n:ℝ)+1)^(2*v)*(c^2*resolventNormResidual Y (n+1)) := by positivity
    have he0 : 0 ≤ E*D*((n:ℝ)+1)^(2*v)*F := by positivity
    dsimp [C0]
    nlinarith
  rw [rational_combination_eval Y v c hden,mul_pow,rationalSechMoment_combination hY]
  have hh:=mul_le_mul_of_nonneg_left hb (sq_nonneg (Y^2-v^2))
  simpa only [F,z,mul_assoc] using hh
noncomputable def rationalPolynomialChristoffel (Y : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ r=P.eval x^2/rationalSechMoment Y 2 (P^2)}
lemma rational_polynomial_ratio_bound {Y v : ℝ} {K : ℝ} (hK : 0 < K)
    {n : ℕ} (h : ∀ P : Polynomial ℝ,P.natDegree ≤ n → P.eval (-(v^2))^2 ≤ K*rationalSechMoment Y 2 (P^2))
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n) :
    P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2) ≤ K := by
  rcases (rationalSechMoment_sq_nonneg Y 2 P).eq_or_lt with hz|hp
  · rw [←hz,div_zero]
    exact hK.le
  · exact (div_le_iff₀ hp).2 (h P hP)
lemma rationalPolynomialChristoffel_upper {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n:ℕ in atTop,rationalPolynomialChristoffel Y n (-(v^2)) ≤ C*((n:ℝ)+1)^(2*v) := by
  obtain ⟨C,hC,h⟩:=rational_polynomial_evaluation_bound hY hv hgap
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with n hn
  have hnonempty : {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ r=P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2)}.Nonempty :=
    ⟨_,0,by simp, rfl⟩
  apply csSup_le hnonempty
  rintro r ⟨P,hP,rfl⟩
  exact rational_polynomial_ratio_bound (by positivity) hn P hP
lemma rationalPolynomialChristoffel_bounds {Y v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hgap : v+1 < Y) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n:ℕ in atTop,
      c*((n:ℝ)+1)^(2*v) ≤ rationalPolynomialChristoffel Y (n+1) (-(v^2)) ∧
      rationalPolynomialChristoffel Y (n+1) (-(v^2)) ≤ C*((n:ℝ)+1)^(2*v) := by
  obtain ⟨a,A,ha,hA,h⟩:=polynomialChristoffel_bounds hv
  obtain ⟨B,hB,hb⟩:=rational_polynomial_evaluation_bound hY hv hgap
  obtain ⟨d,D,hd,hD,hshift⟩:=nat_power_shift_bounds (2*v)
  have hden : Y^2-v^2 ≠ 0 := by nlinarith
  refine ⟨(Y^2-v^2)^2*a,B*D,by positivity,by positivity,?_⟩
  have hb' : ∀ᶠ n:ℕ in atTop,∀ P : Polynomial ℝ,P.natDegree ≤ n+1 → P.eval (-(v^2))^2 ≤ B*((((n+1:ℕ):ℝ))+1)^(2*v)*rationalSechMoment Y 2 (P^2) := (tendsto_add_atTop_nat 1).eventually hb
  filter_upwards [h,hb'] with n hn hbn
  have hbound : BddAbove {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n+1 ∧ r=P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2)} := by
    refine ⟨B*((((n+1:ℕ):ℝ))+1)^(2*v),?_⟩
    rintro r ⟨P,hP,rfl⟩
    exact rational_polynomial_ratio_bound (by positivity) hbn P hP
  constructor
  · obtain ⟨Q,hQ,hQe⟩:=polynomial_evaluation_ratio_attained n (-(v^2))
    let P := (X+Polynomial.C (Y^2))*Q
    have hP : P.natDegree ≤ n+1 := by
      apply (Polynomial.natDegree_mul_le).trans
      have hlin : (X+Polynomial.C (Y^2)).natDegree ≤ 1 := by
        apply natDegree_add_le_of_degree_le (by simp) (by simp)
      omega
    have hPe : P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2)=(Y^2-v^2)^2*polynomialChristoffel n (-(v^2)) := by
      have hm : rationalSechMoment Y 2 (P^2)=polynomialSechInner Q Q := by
        dsimp [P]
        rw [mul_pow,rationalSechMoment_den_twice hY,show Q^2=Q*Q by ring,rationalSechMoment_zero_mul]
      rw [hm]
      dsimp [P]
      simp only [eval_mul,eval_add,eval_X,eval_C]
      rw [show -(v^2)+Y^2=Y^2-v^2 by ring,mul_pow,mul_div_assoc,hQe,polynomialChristoffel_eq_sum]
    have hs : P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2) ≤ rationalPolynomialChristoffel Y (n+1) (-(v^2)) :=
      le_csSup hbound ⟨P,hP,rfl⟩
    rw [hPe] at hs
    apply le_trans _ hs
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hn.1 (sq_nonneg (Y^2-v^2))
  · have hu : rationalPolynomialChristoffel Y (n+1) (-(v^2)) ≤ B*((((n+1:ℕ):ℝ))+1)^(2*v) := by
      have hne : {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n+1 ∧ r=P.eval (-(v^2))^2/rationalSechMoment Y 2 (P^2)}.Nonempty := ⟨_,0,by simp,rfl⟩
      apply csSup_le hne
      rintro r ⟨P,hP,rfl⟩
      exact rational_polynomial_ratio_bound (by positivity) hbn P hP
    have hh:=mul_le_mul_of_nonneg_left (hshift n).2 hB.le
    have hn2 : (n:ℝ)+2=((n+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [hn2] at hh
    exact hu.trans (by simpa [mul_assoc] using hh)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real MeasureTheory Filter Topology
noncomputable def sechWeight (c p : ℝ) : ℝ := (2*c/Real.pi)/Real.cosh (c*p)
noncomputable def rationalSechWeight (c Y p : ℝ) : ℝ := sechWeight c p/(p^2+Y^2)^2
lemma sechWeight_pos {c : ℝ} (hc : 0 < c) (p : ℝ) : 0 < sechWeight c p := by
  unfold sechWeight; positivity
lemma rationalSechWeight_pos {c Y : ℝ} (hc : 0 < c) (hY : 0 < Y) (p : ℝ) : 0 < rationalSechWeight c Y p :=
  div_pos (sechWeight_pos hc p) (sq_pos_of_pos (by positivity))
lemma sechWeight_moments {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*sechWeight c p) (Set.Ioi 0) := by
  apply ((pow_sech_integrable k hc).const_mul (2*c/Real.pi)).congr
  filter_upwards with p
  unfold sechWeight
  ring
lemma rationalSechWeight_moments {c Y : ℝ} (hc : 0 < c) (hY : 0 < Y) (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*rationalSechWeight c Y p) (Set.Ioi 0) := by
  have hden p : 0 < p^2+Y^2 := by positivity
  apply ((sechWeight_moments hc k).norm.div_const ((Y^2)^2)).mono'
  · exact (by unfold rationalSechWeight sechWeight;fun_prop : Measurable (fun p : ℝ=>p^k*rationalSechWeight c Y p)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hw := (sechWeight_pos hc p).le
    simp only [rationalSechWeight,←mul_div_assoc,Real.norm_eq_abs,
      abs_of_pos (sq_pos_of_pos (hden p)),abs_div,abs_of_nonneg (mul_nonneg (pow_nonneg hp.le k) hw)]
    exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hp.le k) hw) (by positivity) (by gcongr;exact le_add_of_nonneg_left (sq_nonneg p))
lemma weightedNorm_sech (c : ℝ) (P : Polynomial ℝ) :
    weightedPolynomialNorm (sechWeight c) P=scaledSechInner c P P := by
  unfold weightedPolynomialNorm scaledSechInner sechExpectation sechWeight
  rw [←integral_const_mul]
  congr 1
  ext p
  ring
lemma weightedKernel_sech (c : ℝ) (n : ℕ) (x : ℝ) :
    weightedPolynomialChristoffel (sechWeight c) n x=scaledPolynomialChristoffel c n x := by
  simp only [weightedPolynomialChristoffel,scaledPolynomialChristoffel,weightedNorm_sech]
lemma weightedNorm_rationalSech (c Y : ℝ) (P : Polynomial ℝ) :
    weightedPolynomialNorm (rationalSechWeight c Y) P=
      sechExpectation c (fun x=>P.eval x^2/(x+Y^2)^2) := by
  unfold weightedPolynomialNorm rationalSechWeight sechWeight sechExpectation
  rw [←integral_const_mul]
  congr 1
  ext p
  ring
lemma weightedNorm_rationalSech_scale {c : ℝ} (hc : 0 < c) (Y : ℝ) (P : Polynomial ℝ) :
    weightedPolynomialNorm (rationalSechWeight c Y) P=
      (c/Real.pi)^4*rationalSechMoment (c*Y/Real.pi) 2 ((polynomialDilate ((Real.pi/c)^2) P)^2) := by
  rw [weightedNorm_rationalSech,sechExpectation_scale hc]
  unfold sechExpectation rationalSechMoment
  simp only [mul_div_cancel_right₀ _ Real.pi_ne_zero,eval_pow,polynomialDilate_eval]
  rw [mul_left_comm ((c/Real.pi)^4) 2]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  have hd : (Real.pi/c)^2*p^2+Y^2=(Real.pi/c)^2*(p^2+(c*Y/Real.pi)^2) := by field_simp
  rw [hd,mul_pow]
  field_simp
lemma rationalSechWeight_evaluation_bound {c Y y : ℝ} (hc : 0 < c) (hY : 0 < Y) (hy : 0 < y)
    (hgap : c*y/Real.pi+1 < c*Y/Real.pi) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ P : Polynomial ℝ,P.natDegree ≤ n →
      P.eval (-(y^2))^2 ≤ C*((n:ℝ)+1)^(2*c*y/Real.pi)*weightedPolynomialNorm (rationalSechWeight c Y) P := by
  obtain ⟨B,hB,hb⟩:=rational_polynomial_evaluation_bound (by positivity : 0 < c*Y/Real.pi)
    (by positivity : 0 < c*y/Real.pi) hgap
  refine ⟨B/(c/Real.pi)^4,by positivity,?_⟩
  filter_upwards [hb] with n hn P hP
  have h:=hn (polynomialDilate ((Real.pi/c)^2) P) ((polynomialDilate_degree _ P).trans hP)
  rw [polynomialDilate_eval] at h
  have he : (Real.pi/c)^2*(-((c*y/Real.pi)^2))=-(y^2) := by field_simp
  rw [he] at h
  rw [weightedNorm_rationalSech_scale hc]
  convert h using 1; field_simp
lemma weightedKernel_rationalSech_upper {c Y y : ℝ} (hc : 0 < c) (hY : 0 < Y) (hy : 0 < y)
    (hgap : c*y/Real.pi+1 < c*Y/Real.pi) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      weightedPolynomialChristoffel (rationalSechWeight c Y) n (-(y^2)) ≤ C*((n:ℝ)+1)^(2*c*y/Real.pi) := by
  obtain ⟨C,hC,h⟩:=rationalSechWeight_evaluation_bound hc hY hy hgap
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨P,hP,hPe⟩:=weightedPolynomial_ratio_attained n (-(y^2)) (rationalSechWeight c Y)
    (fun p _=>rationalSechWeight_pos hc hY p) (rationalSechWeight_moments hc hY)
  rw [←hPe]
  by_cases hz : P=0
  · simp only [hz,eval_zero,zero_pow (by omega : 2≠0),zero_div]
    positivity
  · exact (div_le_iff₀ (weightedPolynomialNorm_pos _ (fun p _=>rationalSechWeight_pos hc hY p)
      (rationalSechWeight_moments hc hY) hz)).mpr (hn P hP)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
