import OAI.Combinatorics.HoneycombChords.Meixner
import OAI.Combinatorics.HoneycombChords.PolynomialKernels
import OAI.Combinatorics.HoneycombChords.SechExpectation
import OAI.Combinatorics.HoneycombChords.TransformSurjectivity

namespace OAI

/-!
# Pollaczek orthogonality and polynomial kernels

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory
open Analytic
noncomputable def symmetricSechPair (f g : ℝ → ℝ) : ℝ :=
  ∫ p in Set.Ioi (0:ℝ),(f p*g p+f (-p)*g (-p))/Real.cosh (Real.pi*p)
lemma symmetricSechPair_comm (f g : ℝ → ℝ) : symmetricSechPair f g=symmetricSechPair g f := by
  unfold symmetricSechPair
  congr 1
  funext p
  ring
lemma generator_prefactor (t : ℝ) :
    (1+t^2)^(-(1:ℝ)/2)=Real.cos (Real.arctan t) := by
  rw [Real.cos_arctan,show -(1:ℝ)/2=-((1:ℝ)/2) by ring,Real.rpow_neg (by positivity),Real.sqrt_eq_rpow]
  simp only [one_div]
lemma generator_symmetric_product (t u p : ℝ) :
    pollaczekGenerator p t*pollaczekGenerator p u+
      pollaczekGenerator (-p) t*pollaczekGenerator (-p) u=
    2*(Real.cos (Real.arctan t)*Real.cos (Real.arctan u))*
      Real.cosh ((2*(Real.arctan t+Real.arctan u))*p) := by
  simp only [pollaczekGenerator,generator_prefactor,Real.cosh_eq]
  rw [show -(2*(Real.arctan t+Real.arctan u)*p)=2*(-p)*Real.arctan t+2*(-p)*Real.arctan u by ring,
    show 2*(Real.arctan t+Real.arctan u)*p=2*p*Real.arctan t+2*p*Real.arctan u by ring,
    Real.exp_add,Real.exp_add]
  ring
lemma arctan_quarter_bound {t : ℝ} (ht : |t| < 1) : |Real.arctan t| < Real.pi/4 := by
  obtain ⟨hl,hu⟩ := abs_lt.1 ht
  apply abs_lt.2
  constructor
  · have h := Real.arctan_strictMono hl
    simpa [Real.arctan_neg,Real.arctan_one] using h
  · simpa [Real.arctan_one] using Real.arctan_strictMono hu
lemma symmetricSechPair_generator {t u : ℝ} (ht : |t| < 1) (hu : |u| < 1) :
    symmetricSechPair (fun p=>pollaczekGenerator p t) (fun p=>pollaczekGenerator p u)=
      1/(1-t*u) := by
  have hm : |2*(Real.arctan t+Real.arctan u)| < Real.pi := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have h := abs_add_le (Real.arctan t) (Real.arctan u)
    linarith [arctan_quarter_bound ht,arctan_quarter_bound hu]
  unfold symmetricSechPair
  simp only [generator_symmetric_product]
  simp_rw [mul_div_assoc]
  rw [integral_const_mul,sech_kernel_integral Real.pi_pos hm]
  have hpi : Real.pi*(2*(Real.arctan t+Real.arctan u))/(2*Real.pi)=Real.arctan t+Real.arctan u := by
    field_simp
  rw [hpi,Real.cos_add]
  have hct := (Real.cos_arctan_pos t).ne'
  have hcu := (Real.cos_arctan_pos u).ne'
  have hst : Real.sin (Real.arctan t)=t*Real.cos (Real.arctan t) := by
    rw [Real.sin_arctan,Real.cos_arctan];ring
  have hsu : Real.sin (Real.arctan u)=u*Real.cos (Real.arctan u) := by
    rw [Real.sin_arctan,Real.cos_arctan];ring
  rw [hst,hsu]
  have hh : Real.cos (Real.arctan t)*Real.cos (Real.arctan u)-
      t*Real.cos (Real.arctan t)*(u*Real.cos (Real.arctan u))=
      (Real.cos (Real.arctan t)*Real.cos (Real.arctan u))*(1-t*u) := by ring
  rw [hh]
  field_simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology MeasureTheory
lemma pollaczek_series_bound {H : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ p,|H p| ≤ C*pollaczekMajorant p) {t : ℝ} (ht : |t| ≤ 1/4) (n : ℕ) (p : ℝ) :
    ‖((pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p))/Real.cosh (Real.pi*p))*t^n‖ ≤
      (meixnerCoeff |p| n*(1/4)^n)*(2*C*pollaczekMajorant p/Real.cosh (Real.pi*p)) := by
  have hq := pollaczekCoeff_abs_le p n
  have hqm := pollaczekCoeff_abs_le (-p) n
  have hh := hH p
  have hhm := hH (-p)
  simp only [abs_neg] at hqm
  simp only [pollaczekMajorant,abs_neg] at hhm
  change |H (-p)| ≤ C*pollaczekMajorant p at hhm
  simp only [norm_mul,Real.norm_eq_abs,abs_div,abs_of_pos (Real.cosh_pos _),abs_pow]
  have hb : |pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p)| ≤
      2*(meixnerCoeff |p| n*(C*pollaczekMajorant p)) := by
    calc
      _ ≤ |pollaczekCoeff p n*H p|+|pollaczekCoeff (-p) n*H (-p)| := abs_add_le _ _
      _ ≤ meixnerCoeff |p| n*(C*pollaczekMajorant p)+meixnerCoeff |p| n*(C*pollaczekMajorant p) := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul hq hh (abs_nonneg _) (meixnerCoeff_nonneg (abs_nonneg p) n))
          (mul_le_mul hqm hhm (abs_nonneg _) (meixnerCoeff_nonneg (abs_nonneg p) n))
      _ = _ := by ring
  calc
    _ ≤ (2*(meixnerCoeff |p| n*(C*pollaczekMajorant p))/Real.cosh (Real.pi*p))*(1/4)^n := by
      have hmn := meixnerCoeff_nonneg (abs_nonneg p) n
      have hp := (pollaczekMajorant_pos p).le
      gcongr
    _ = _ := by ring
lemma pollaczek_pair_hasSum {H : ℝ → ℝ} (hHc : Continuous H) {C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ p,|H p| ≤ C*pollaczekMajorant p) {t : ℝ} (ht : |t| ≤ 1/4) :
    HasSum (fun n => symmetricSechPair (fun p=>pollaczekCoeff p n) H*t^n)
      (symmetricSechPair (fun p=>pollaczekGenerator p t) H) := by
  let F : ℕ → ℝ → ℝ := fun n p =>
    ((pollaczekCoeff p n*H p+pollaczekCoeff (-p) n*H (-p))/Real.cosh (Real.pi*p))*t^n
  let bound : ℕ → ℝ → ℝ := fun n p =>
    (meixnerCoeff |p| n*(1/4)^n)*(2*C*pollaczekMajorant p/Real.cosh (Real.pi*p))
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (Set.Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    unfold F
    apply Continuous.mul _ continuous_const
    apply Continuous.div _ (by fun_prop) (fun p => (Real.cosh_pos _).ne')
    exact ((pollaczekCoeff_continuous n).mul hHc).add
      (((pollaczekCoeff_continuous n).comp continuous_neg).mul (hHc.comp continuous_neg))
  have hb (n : ℕ) : ∀ᵐ p ∂volume.restrict (Set.Ioi 0), ‖F n p‖ ≤ bound n p :=
    Eventually.of_forall (pollaczek_series_bound hC hH ht n)
  have hsum (p : ℝ) : HasSum (fun n => bound n p)
      (2*C*(pollaczekMajorant p^2/Real.cosh (Real.pi*p))) := by
    convert! (meixnerCoeff_hasSum |p| (u:=1/4) (by norm_num)).mul_right
      (2*C*pollaczekMajorant p/Real.cosh (Real.pi*p)) using 1
    unfold pollaczekMajorant
    ring
  have hint : Integrable (fun p => ∑' n,bound n p) (volume.restrict (Set.Ioi 0)) := by
    simp_rw [(hsum _).tsum_eq]
    exact pollaczekMajorant_sq_integrable.const_mul (2*C)
  have hlim : ∀ᵐ p ∂volume.restrict (Set.Ioi 0),HasSum (fun n=>F n p)
      ((pollaczekGenerator p t*H p+pollaczekGenerator (-p) t*H (-p))/Real.cosh (Real.pi*p)) := by
    apply Eventually.of_forall
    intro p
    convert! ((pollaczekCoeff_hasSum p (t:=t) (by linarith)).mul_right (H p) |>.add
      ((pollaczekCoeff_hasSum (-p) (t:=t) (by linarith)).mul_right (H (-p)))).div_const
        (Real.cosh (Real.pi*p)) using 1
    funext n
    unfold F
    ring
  have hz := hasSum_integral_of_dominated_convergence bound hmeas hb
    (Eventually.of_forall fun p => (hsum p).summable) hint hlim
  simpa only [F,integral_mul_const,symmetricSechPair] using hz
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
lemma coefficients_unique {f : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : ∀ᶠ t in 𝓝 0, HasSum (fun n=>a n*t^n) (f t))
    (hb : ∀ᶠ t in 𝓝 0, HasSum (fun n=>b n*t^n) (f t)) (n : ℕ) : a n=b n := by
  have ha' : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ a) 0 :=
    hasFPowerSeriesAt_iff.2 (by simpa only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,mul_comm,zero_add] using ha)
  have hb' : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ b) 0 :=
    hasFPowerSeriesAt_iff.2 (by simpa only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,mul_comm,zero_add] using hb)
  exact (scalarSeries_taylor ha' n).symm.trans (scalarSeries_taylor hb' n)
lemma symmetricSechPair_coeff_generator {u : ℝ} (hu : |u| < 1/4) (n : ℕ) :
    symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekGenerator p u)=u^n := by
  refine coefficients_unique (a:=fun n => symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekGenerator p u))
    (b:=fun n=>u^n) (f:=fun t=>1/(1-t*u)) ?_ ?_ n
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1/4)] with t ht
    have ht' : |t| < 1/4 := by simpa [Metric.mem_ball] using ht
    have hs := pollaczek_pair_hasSum (pollaczekGenerator_continuous_p u) (C:=1) (by norm_num)
      (fun p=>by simpa using pollaczekGenerator_majorant p hu.le) ht'.le
    rw [symmetricSechPair_generator (by linarith) (by linarith)] at hs
    exact hs
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with t ht
    have ht' : |t| < 1 := by simpa [Metric.mem_ball] using ht
    have hp : ‖t*u‖ < 1 := by rw [Real.norm_eq_abs,abs_mul];nlinarith [abs_nonneg t,abs_nonneg u]
    simpa [mul_pow,mul_comm,one_div] using hasSum_geometric_of_norm_lt_one hp
lemma symmetricSechPair_orthogonal (n m : ℕ) :
    symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekCoeff p m)=if n=m then 1 else 0 := by
  refine coefficients_unique (a:=fun n => symmetricSechPair (fun p=>pollaczekCoeff p n) (fun p=>pollaczekCoeff p m))
    (b:=fun n=>if n=m then 1 else 0) (f:=fun t:ℝ=>t^m) ?_ ?_ n
  · filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1/4)] with t ht
    have ht' : |t| < 1/4 := by simpa [Metric.mem_ball] using ht
    have hs := pollaczek_pair_hasSum (pollaczekCoeff_continuous m) (C:=4^m) (by positivity)
      (fun p=>pollaczekCoeff_majorant p m) ht'.le
    rw [symmetricSechPair_comm,symmetricSechPair_coeff_generator ht'] at hs
    exact hs
  · apply Eventually.of_forall
    intro t
    convert! (hasSum_ite_eq m (t^m)) using 1
    funext j
    by_cases hj : j=m <;> simp [hj]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial
lemma meixnerCoeff_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < meixnerCoeff s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [meixnerCoeff]
  | one => simp only [meixnerCoeff];positivity
  | more n ih0 ih1 => rw [meixnerCoeff];positivity
lemma evenPoly_ne_zero (n : ℕ) : evenPoly (-1) n ≠ 0 := by
  intro h
  have he := evenPoly_negative_eval 1 n
  rw [h] at he
  simp only [eval_zero] at he
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (meixnerCoeff_pos (by norm_num : (0:ℝ)<1) _).ne' he.symm
lemma oddPoly_ne_zero (n : ℕ) : oddPoly (-1) n ≠ 0 := by
  intro h
  have he := (evenOdd_sign_eval 1 n).2
  rw [h] at he
  have hh := (evenOdd_plus_eval 1 n).2
  simp only [one_pow,one_mul] at hh
  rw [hh] at he
  simp only [eval_zero] at he
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (meixnerCoeff_pos (by norm_num : (0:ℝ)<1) _).ne' he.symm
lemma pollaczek_evenOdd_degree (n : ℕ) :
    (evenPoly (-1) n).natDegree=n ∧ (oddPoly (-1) n).natDegree=n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc2 : (2:ℝ) ≠ 0 := by norm_num
    have hE : (evenPoly (-1) (n+1)).natDegree=n+1 := by
      rw [evenPoly_succ,natDegree_C_mul (by positivity),mul_assoc,natDegree_add_eq_left_of_natDegree_lt]
      · rw [natDegree_C_mul hc2,natDegree_X_mul (oddPoly_ne_zero n),ih.2]
      · rw [natDegree_C_mul hc2,natDegree_X_mul (oddPoly_ne_zero n)]
        exact (natDegree_C_mul_le _ _).trans_lt (by rw [ih.1,ih.2];omega)
    refine ⟨hE,?_⟩
    rw [oddPoly_succ,natDegree_C_mul (by positivity),natDegree_add_eq_left_of_natDegree_lt]
    · rw [natDegree_C_mul hc2,hE]
    · rw [natDegree_C_mul hc2,hE]
      exact (natDegree_C_mul_le _ _).trans_lt (by rw [ih.2];omega)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset
lemma pollaczek_span (N : ℕ) :
    Submodule.span ℝ ((fun j:ℕ=>(X:Polynomial ℝ)^j) '' Set.Iio N)=
      Submodule.span ℝ ((evenPoly (-1)) '' Set.Iio N) := by
  apply Analytic.triangular_span (fun j:ℕ=>(X:Polynomial ℝ)^j) (evenPoly (-1))
    (fun k j => (evenPoly (-1) k).coeff j)
  · intro k
    have h := (evenPoly (-1) k).as_sum_range_C_mul_X_pow
    rw [(pollaczek_evenOdd_degree k).1] at h
    simpa only [Polynomial.smul_eq_C_mul] using h
  · intro k
    have h := Polynomial.leadingCoeff_ne_zero.mpr (evenPoly_ne_zero k)
    rwa [←Polynomial.coeff_natDegree,(pollaczek_evenOdd_degree k).1] at h
lemma polynomial_eq_pollaczek_sum (p : Polynomial ℝ) {n : ℕ} (hn : p.natDegree ≤ n) :
    ∃ a : Fin (n+1) → ℝ,∑ j,a j • evenPoly (-1) j=p := by
  have hp : p ∈ Submodule.span ℝ ((fun j:ℕ=>(X:Polynomial ℝ)^j) '' Set.Iio (n+1)) := by
    rw [p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < n+1)]
    apply Submodule.sum_mem
    intro j hj
    rw [←Polynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,mem_range.mp hj,rfl⟩)
  rw [pollaczek_span] at hp
  have he : (evenPoly (-1)) '' Set.Iio (n+1)=Set.range (fun j:Fin (n+1)=>evenPoly (-1) j) := by
    ext p
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨j,j.isLt,rfl⟩
  rw [he] at hp
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real MeasureTheory
lemma pow_sech_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun p:ℝ=>p^n/Real.cosh (c*p)) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun p:ℝ=>2*(p^n*Real.exp (-c*p))) (Set.Ioi 0) := by
    simpa only [IntegrableOn, Real.rpow_natCast, Real.rpow_one, neg_mul] using (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=(n:ℝ)) (p:=1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (by norm_num) hc).const_mul 2
  have hm : Continuous (fun p:ℝ=>p^n/Real.cosh (c*p)) :=
    (show Continuous (fun p:ℝ=>p^n) by fun_prop).div (by fun_prop) (fun _=>(Real.cosh_pos _).ne')
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have hp0 : 0 ≤ p := le_of_lt hp
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh : Real.exp (c*p)/2 ≤ Real.cosh (c*p) := by
    rw [Real.cosh_eq];linarith [Real.exp_pos (-(c*p))]
  calc
    _ ≤ p^n/(Real.exp (c*p)/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hh
    _ = _ := by rw [neg_mul,Real.exp_neg];ring
lemma polynomial_sech_integrable (P : Polynomial ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun p:ℝ=>P.eval (p^2)/Real.cosh (c*p)) (Set.Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    apply (hP.add hQ).congr
    filter_upwards with p
    simp only [eval_add,Pi.add_apply,add_div]
  | monomial n a =>
    apply ((pow_sech_integrable (2*n) hc).const_mul a).congr
    filter_upwards with p
    simp only [eval_monomial,pow_mul]
    ring
lemma polynomial_sech_pair_integrable (P Q : Polynomial ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun p:ℝ=>P.eval (p^2)*Q.eval (p^2)/Real.cosh (c*p)) (Set.Ioi 0) := by
  simpa only [eval_mul] using polynomial_sech_integrable (P*Q) hc
noncomputable def polynomialSechInner (P Q : Polynomial ℝ) : ℝ :=
  sechExpectation Real.pi (fun x=>P.eval x*Q.eval x)
lemma polynomialSechInner_eq (P Q : Polynomial ℝ) :
    polynomialSechInner P Q=2*∫ p in Set.Ioi (0:ℝ),P.eval (p^2)*Q.eval (p^2)/Real.cosh (Real.pi*p) := by
  unfold polynomialSechInner sechExpectation
  rw [mul_div_cancel_right₀ _ Real.pi_ne_zero]
lemma polynomialSechInner_orthogonal (n m : ℕ) :
    polynomialSechInner (evenPoly (-1) n) (evenPoly (-1) m)=if n=m then 1 else 0 := by
  have h := symmetricSechPair_orthogonal (2*n) (2*m)
  have he : polynomialSechInner (evenPoly (-1) n) (evenPoly (-1) m)=
      symmetricSechPair (fun p=>pollaczekCoeff p (2*n)) (fun p=>pollaczekCoeff p (2*m)) := by
    rw [polynomialSechInner_eq,symmetricSechPair,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    rw [←(pollaczekCoeff_evenOdd p n).1,←(pollaczekCoeff_evenOdd p m).1,
      ←(pollaczekCoeff_evenOdd (-p) n).1,←(pollaczekCoeff_evenOdd (-p) m).1]
    simp only [neg_sq]
    ring
  rw [he,h]
  have hnm : (2*n=2*m) ↔ n=m := by omega
  simp only [hnm]
lemma polynomialSechInner_sum_left {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (Q : Polynomial ℝ) :
    polynomialSechInner (∑ i∈s,P i) Q=∑ i∈s,polynomialSechInner (P i) Q := by
  simp only [polynomialSechInner_eq,eval_finsetSum,Finset.sum_mul,Finset.sum_div]
  rw [integral_finsetSum s (fun i _=>polynomial_sech_pair_integrable _ _ Real.pi_pos),Finset.mul_sum]
lemma polynomialSechInner_smul_left (a : ℝ) (P Q : Polynomial ℝ) :
    polynomialSechInner (a • P) Q=a*polynomialSechInner P Q := by
  simp only [polynomialSechInner_eq,eval_smul,smul_eq_mul]
  simp_rw [mul_assoc,mul_div_assoc]
  rw [integral_const_mul]
  ring
lemma polynomialSechInner_comm (P Q : Polynomial ℝ) : polynomialSechInner P Q=polynomialSechInner Q P := by
  simp only [polynomialSechInner_eq,mul_comm]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Real Filter Topology
noncomputable def pollaczekCombination {n : ℕ} (a : Fin (n+1) → ℝ) : Polynomial ℝ :=
  ∑ j,a j • evenPoly (-1) j
lemma pollaczekCombination_eval {n : ℕ} (a : Fin (n+1) → ℝ) (x : ℝ) :
    (pollaczekCombination a).eval x=∑ j,a j*(evenPoly (-1) j).eval x := by
  simp only [pollaczekCombination,eval_finsetSum,eval_smul,smul_eq_mul]
lemma pollaczekCombination_inner {n : ℕ} (a : Fin (n+1) → ℝ) :
    polynomialSechInner (pollaczekCombination a) (pollaczekCombination a)=∑ j,a j^2 := by
  rw [pollaczekCombination,polynomialSechInner_sum_left]
  apply sum_congr rfl
  intro j _
  rw [polynomialSechInner_smul_left,polynomialSechInner_comm,polynomialSechInner_sum_left]
  simp only [polynomialSechInner_smul_left,polynomialSechInner_orthogonal,Fin.val_inj,
    mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true,pow_two]
lemma pollaczekCombination_degree {n : ℕ} (a : Fin (n+1) → ℝ) :
    (pollaczekCombination a).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_smul_le _ _).trans (by rw [(pollaczek_evenOdd_degree j).1];omega)
noncomputable def sechChristoffelSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j:Fin (n+1),((evenPoly (-1) j).eval x)^2
lemma sechChristoffelSum_pos (n : ℕ) (x : ℝ) : 0 < sechChristoffelSum n x := by
  have h := Finset.single_le_sum (f:=fun j:Fin (n+1)=>((evenPoly (-1) j).eval x)^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ (⟨0,by omega⟩:Fin (n+1)))
  simp only [evenPoly_zero,eval_one,one_pow] at h
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) h
lemma polynomialSechInner_nonneg (P : Polynomial ℝ) : 0 ≤ polynomialSechInner P P := by
  obtain ⟨a,ha⟩ := polynomial_eq_pollaczek_sum P le_rfl
  rw [←ha]
  change 0 ≤ polynomialSechInner (pollaczekCombination a) (pollaczekCombination a)
  rw [pollaczekCombination_inner]
  exact sum_nonneg (fun j _=>sq_nonneg _)
lemma polynomial_evaluation_bound (P : Polynomial ℝ) {n : ℕ} (hP : P.natDegree ≤ n) (x : ℝ) :
    P.eval x^2 ≤ polynomialSechInner P P*sechChristoffelSum n x := by
  obtain ⟨a,ha⟩ := polynomial_eq_pollaczek_sum P hP
  change pollaczekCombination a=P at ha
  rw [←ha,pollaczekCombination_eval,pollaczekCombination_inner]
  exact sum_mul_sq_le_sq_mul_sq _ _ _
lemma polynomial_evaluation_ratio_bound (P : Polynomial ℝ) {n : ℕ} (hP : P.natDegree ≤ n) (x : ℝ) :
    P.eval x^2/polynomialSechInner P P ≤ sechChristoffelSum n x := by
  rcases (polynomialSechInner_nonneg P).eq_or_lt with hz|hp
  · rw [←hz,div_zero]
    exact (sechChristoffelSum_pos n x).le
  · apply (div_le_iff₀ hp).2
    simpa only [mul_comm] using polynomial_evaluation_bound P hP x
lemma polynomial_evaluation_ratio_attained (n : ℕ) (x : ℝ) :
    ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ P.eval x^2/polynomialSechInner P P=sechChristoffelSum n x := by
  let a : Fin (n+1) → ℝ := fun j=>(evenPoly (-1) j).eval x
  refine ⟨pollaczekCombination a,pollaczekCombination_degree a,?_⟩
  rw [pollaczekCombination_eval,pollaczekCombination_inner]
  change (∑ j,a j*a j)^2/(∑ j,a j^2)=sechChristoffelSum n x
  simp only [←pow_two]
  change (sechChristoffelSum n x)^2/sechChristoffelSum n x=sechChristoffelSum n x
  rw [pow_two,mul_div_cancel_right₀ _ (sechChristoffelSum_pos n x).ne']
noncomputable def polynomialChristoffel (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ r=P.eval x^2/polynomialSechInner P P}
lemma polynomialChristoffel_eq_sum (n : ℕ) (x : ℝ) : polynomialChristoffel n x=sechChristoffelSum n x := by
  obtain ⟨P,hP,hPe⟩ := polynomial_evaluation_ratio_attained n x
  have hm : sechChristoffelSum n x ∈ {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ r=P.eval x^2/polynomialSechInner P P} :=
    ⟨P,hP,hPe.symm⟩
  apply le_antisymm
  · apply csSup_le ⟨_,hm⟩
    rintro r ⟨Q,hQ,rfl⟩
    exact polynomial_evaluation_ratio_bound Q hQ x
  · apply le_csSup _ hm
    refine ⟨sechChristoffelSum n x,?_⟩
    rintro r ⟨Q,hQ,rfl⟩
    exact polynomial_evaluation_ratio_bound Q hQ x
lemma polynomialChristoffel_negative (s : ℝ) (n : ℕ) :
    polynomialChristoffel n (-(s^2))=evenCoefficientKernel s n := by
  rw [polynomialChristoffel_eq_sum]
  simp only [sechChristoffelSum,evenPoly_negative_eval_sq,evenCoefficientKernel,←Fin.sum_univ_eq_sum_range]
/-- Source Christoffel estimate for the genuine normalized sech measure at
c=pi, not just the formal generating coefficients. -/
theorem polynomialChristoffel_bounds {s : ℝ} (hs : 0 < s) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c*((n:ℝ)+1)^(2*s) ≤ polynomialChristoffel n (-(s^2)) ∧
      polynomialChristoffel n (-(s^2)) ≤ C*((n:ℝ)+1)^(2*s) := by
  simpa only [polynomialChristoffel_negative] using evenCoefficientKernel_bounds hs
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real MeasureTheory Filter Topology
lemma sechExpectation_scale {c : ℝ} (hc : 0 < c) (H : ℝ → ℝ) :
    sechExpectation c H=sechExpectation Real.pi (fun x=>H ((Real.pi/c)^2*x)) := by
  have ht:=integral_comp_mul_left_Ioi
    (fun q : ℝ=>H ((Real.pi/c)^2*q^2)/Real.cosh (Real.pi*q)) 0
    (by positivity : 0 < c/Real.pi)
  have he (p : ℝ) : H ((Real.pi/c)^2*(c/Real.pi*p)^2)/Real.cosh (Real.pi*(c/Real.pi*p))=
      H (p^2)/Real.cosh (c*p) := by
    congr 2 <;> field_simp
  simp only [he,mul_zero,smul_eq_mul] at ht
  unfold sechExpectation
  rw [ht,mul_div_cancel_right₀ _ Real.pi_ne_zero]
  field_simp
noncomputable def polynomialDilate (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.C a*X)
lemma polynomialDilate_eval (a : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    (polynomialDilate a P).eval x=P.eval (a*x) := by simp [polynomialDilate]
lemma polynomialDilate_degree (a : ℝ) (P : Polynomial ℝ) :
    (polynomialDilate a P).natDegree ≤ P.natDegree := by
  unfold polynomialDilate
  calc
    _ ≤ P.natDegree*(Polynomial.C a*X).natDegree := natDegree_comp_le
    _ ≤ P.natDegree*1 := Nat.mul_le_mul_left _ (by simpa using (natDegree_mul_le (p:=Polynomial.C a) (q:=X)))
    _ = _ := Nat.mul_one _
lemma polynomialDilate_mul (a b : ℝ) (P : Polynomial ℝ) :
    polynomialDilate a (polynomialDilate b P)=polynomialDilate (b*a) P := by
  apply Polynomial.funext
  intro x
  simp only [polynomialDilate_eval]
  congr 1
  ring
noncomputable def scaledSechInner (c : ℝ) (P Q : Polynomial ℝ) : ℝ :=
  sechExpectation c (fun x=>P.eval x*Q.eval x)
lemma scaledSechInner_eq {c : ℝ} (hc : 0 < c) (P Q : Polynomial ℝ) :
    scaledSechInner c P Q=polynomialSechInner (polynomialDilate ((Real.pi/c)^2) P)
      (polynomialDilate ((Real.pi/c)^2) Q) := by
  rw [scaledSechInner,sechExpectation_scale hc]
  simp only [polynomialSechInner,polynomialDilate_eval]
noncomputable def scaledPolynomialChristoffel (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ P : Polynomial ℝ,P.natDegree ≤ n ∧ r=P.eval x^2/scaledSechInner c P P}
lemma scaledPolynomialChristoffel_eq {c : ℝ} (hc : 0 < c) (n : ℕ) (x : ℝ) :
    scaledPolynomialChristoffel c n x=polynomialChristoffel n ((c/Real.pi)^2*x) := by
  unfold scaledPolynomialChristoffel polynomialChristoffel
  congr 1
  ext r
  constructor
  · rintro ⟨P,hP,rfl⟩
    refine ⟨polynomialDilate ((Real.pi/c)^2) P,(polynomialDilate_degree _ P).trans hP,?_⟩
    rw [scaledSechInner_eq hc,polynomialDilate_eval]
    congr 3
    field_simp
  · rintro ⟨P,hP,rfl⟩
    refine ⟨polynomialDilate ((c/Real.pi)^2) P,(polynomialDilate_degree _ P).trans hP,?_⟩
    rw [scaledSechInner_eq hc,polynomialDilate_mul,polynomialDilate_eval]
    have he : (c/Real.pi)^2*(Real.pi/c)^2=1 := by field_simp
    rw [he]
    simp only [polynomialDilate,Polynomial.C_1,one_mul,comp_X]
/-- Inverse Christoffel kernel for the actual normalized sech measure at
arbitrary positive decay rate, evaluated at a fixed negative square. -/
theorem scaledPolynomialChristoffel_bounds {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*(n+1:ℝ)^(2*c*y/Real.pi) ≤ scaledPolynomialChristoffel c n (-(y^2)) ∧
      scaledPolynomialChristoffel c n (-(y^2)) ≤ C*(n+1:ℝ)^(2*c*y/Real.pi) := by
  have he (n : ℕ) : scaledPolynomialChristoffel c n (-(y^2))=
      polynomialChristoffel n (-((c*y/Real.pi)^2)) := by
    rw [scaledPolynomialChristoffel_eq hc]
    congr 2
    ring
  simpa only [he,show 2*(c*y/Real.pi)=2*c*y/Real.pi by ring] using
    polynomialChristoffel_bounds (by positivity : 0 < c*y/Real.pi)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
