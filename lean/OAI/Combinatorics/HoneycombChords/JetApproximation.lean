import OAI.Combinatorics.HoneycombChords.FourierApproximation
import OAI.Combinatorics.HoneycombChords.StripProducts

namespace OAI

/-!
# Polynomial approximation of complete strip jets

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
/- Necessary coefficient estimate for the actual two-jet polynomial
approximation in UniformMarked, strip-asymptotics.tex:85--86. -/
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Polynomial
lemma integerGapProduct (n : ℕ) (i : Fin (n+1)) :
    (∏ j : Fin (n+1),if j=i then (1:ℝ) else |(i:ℝ)-(j:ℝ)|)=
      (Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ) := by
  induction n with
  | zero => fin_cases i;simp
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last,ite_true,Fin.castSucc_ne_last,ite_false,Fin.val_castSucc,mul_one]
      have he : (∏ j : Fin (n+1),|((n+1:ℕ):ℝ)-(j:ℝ)|)=((n+1).factorial:ℝ) := by
        rw [Fin.prod_univ_eq_prod_range (fun j : ℕ=>|((n+1:ℕ):ℝ)-(j:ℝ)|)]
        rw [show (∏ j∈range (n+1),|((n+1:ℕ):ℝ)-(j:ℝ)|)=∏ j∈range (n+1),(((n+1)-j:ℕ):ℝ) from by
          apply prod_congr rfl
          intro j hj
          have hj' : j ≤ n+1 := (mem_range.mp hj).le
          rw [Nat.cast_sub hj',abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj'))]]
        exact_mod_cast (Nat.descFactorial_eq_prod_range (n+1) (n+1)).symm.trans (Nat.descFactorial_self (n+1))
      rw [he]
      simp
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.castSucc_inj,Fin.val_castSucc,Ne.symm (Fin.castSucc_ne_last i),ite_false,Fin.val_last,ih i]
      have hi : i.val ≤ n := by omega
      have habs : |(i:ℝ)-((n+1:ℕ):ℝ)|=((n+1-i.val:ℕ):ℝ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show i.val ≤ n+1 by omega))),Nat.cast_sub (by omega)]
        ring
      rw [habs,show n+1-i.val=(n-i.val)+1 by omega,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Polynomial
lemma integerGapProduct_erase (n : ℕ) (i : Fin (n+1)) :
    (∏ j∈(univ.erase i),|(i:ℝ)-(j:ℝ)|)=(Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ) := by
  rw [←integerGapProduct n i]
  rw [←prod_erase_mul (s:=univ) (f:=fun j : Fin (n+1)=>if j=i then (1:ℝ) else |(i:ℝ)-(j:ℝ)|) (mem_univ i)]
  simp only [ite_true,mul_one]
  apply prod_congr rfl
  intro j hj
  simp only [(mem_erase.mp hj).1,ite_false]
lemma integer_lagrange_basis_bound (n : ℕ) (a x : ℝ) (ha : 0 ≤ a) (hx : a+(n:ℝ) ≤ x) (i : Fin (n+1)) :
    |(Lagrange.basis univ (fun j : Fin (n+1)=>a+(j:ℝ)) i).eval x| ≤
      x^n/((Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ)) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have he : |(Lagrange.basis univ (fun j : Fin (n+1)=>a+(j:ℝ)) i).eval x|=
      (∏ j∈univ.erase i,|x-(a+(j:ℝ))|)/(∏ j∈univ.erase i,|(i:ℝ)-(j:ℝ)|) := by
    simp only [Lagrange.basis,eval_prod,Lagrange.basisDivisor,eval_mul,eval_C,eval_sub,eval_X,
      abs_prod,abs_mul,abs_inv]
    simp_rw [show ∀ j : Fin (n+1),a+(i:ℝ)-(a+(j:ℝ))=(i:ℝ)-(j:ℝ) from fun _=>by ring]
    rw [prod_mul_distrib,prod_inv_distrib]
    ring
  rw [he,integerGapProduct_erase]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∏ j∈(univ.erase i),x := by
      apply prod_le_prod₀ (fun _ _=>abs_nonneg _)
      intro j hj
      have hjn : (j:ℝ) ≤ n := by exact_mod_cast (show j.val ≤ n by omega)
      rw [abs_of_nonneg (by linarith)]
      linarith [show (0:ℝ) ≤ (j:ℝ) by positivity]
    _ = x^n := by simp
lemma integer_polynomial_bound (n : ℕ) (a x B : ℝ) (ha : 0 ≤ a) (hx : a+(n:ℝ) ≤ x) (hB : 0 ≤ B)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n) (hvalues : ∀ i : Fin (n+1),|P.eval (a+(i:ℝ))| ≤ B) :
    |P.eval x| ≤ B*(2*x)^n/(Nat.factorial n:ℝ) := by
  have hinj : Set.InjOn (fun j : Fin (n+1)=>a+(j:ℝ)) (↑(univ : Finset (Fin (n+1)))) := by
    intro i _ j _ hij
    apply Fin.ext
    exact_mod_cast add_left_cancel hij
  have hdeg : P.degree < ((univ : Finset (Fin (n+1))).card:WithBot ℕ) := by
    simp only [card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (show P.natDegree<n+1 by omega))
  have he := Lagrange.eq_interpolate hinj hdeg
  have he' := congrArg (fun Q : Polynomial ℝ=>Q.eval x) he
  simp only [Lagrange.interpolate,LinearMap.coe_mk,AddHom.coe_mk,eval_finsetSum,eval_mul,eval_C] at he'
  rw [he']
  calc
    _ ≤ ∑ i : Fin (n+1),|P.eval (a+(i:ℝ))| *|(Lagrange.basis univ (fun j : Fin (n+1)=>a+(j:ℝ)) i).eval x| := by
      simpa only [abs_mul] using abs_sum_le_sum_abs (fun i : Fin (n+1)=>P.eval (a+(i:ℝ))*(Lagrange.basis univ (fun j : Fin (n+1)=>a+(j:ℝ)) i).eval x) univ
    _ ≤ ∑ i : Fin (n+1),B*(x^n/((Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ))) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul (hvalues i) (integer_lagrange_basis_bound n a x ha hx i) (abs_nonneg _) hB
    _ = B*(2*x)^n/(Nat.factorial n:ℝ) := by
      have hb (i : Fin (n+1)) : B*(x^n/((Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ)))=
          (B*x^n/(Nat.factorial n:ℝ))*(Nat.choose n i.val:ℝ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (show i.val ≤ n by omega)
        have hf : (Nat.choose n i.val:ℝ)*(Nat.factorial i.val:ℝ)*(Nat.factorial (n-i.val):ℝ)=(Nat.factorial n:ℝ) := by exact_mod_cast h
        field_simp
        linear_combination -B*x^n*hf
      simp_rw [hb]
      rw [←mul_sum,Fin.sum_univ_eq_sum_range (fun i : ℕ => (Nat.choose n i:ℝ))]
      have hs : (∑ i∈range (n+1),(Nat.choose n i:ℝ))=(2:ℝ)^n := by exact_mod_cast Nat.sum_range_choose n
      rw [hs,mul_pow]
      ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Polynomial
/-- Quantitative Lagrange bound, with an arbitrarily small exponential instead
of a Stirling asymptotic. Used on the literal q^j p(j) Pollaczek tails. -/
lemma integer_polynomial_exponential_bound (n : ℕ) (a x B α : ℝ)
    (ha : 0 ≤ a) (hx : a+(n:ℝ) ≤ x) (hB : 0 ≤ B) (hα : 0<α)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ n)
    (hvalues : ∀ i : Fin (n+1),|P.eval (a+(i:ℝ))| ≤ B) :
    |P.eval x| ≤ B*(2/α)^n*Real.exp (α*x) := by
  refine (integer_polynomial_bound n a x B ha hx hB P hP hvalues).trans ?_
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  calc
    B*(2*x)^n/(Nat.factorial n:ℝ)=B*(2/α)^n*((α*x)^n/(Nat.factorial n:ℝ)) := by
      rw [mul_pow,mul_pow,div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (mul_nonneg hα.le hx0) n) (by positivity)
lemma exp_power_bound (A γ : ℝ) (hA : 1 ≤ A) (hγ : 0<γ) (n j : ℕ)
    (hnj : (4*(2*γ+Real.log A)/γ)*(n:ℝ) ≤ j) :
    Real.exp (-γ*(j:ℝ))*Real.exp (2*γ*(n:ℝ))*A^n*Real.exp (γ/4*(j:ℝ)) ≤
      Real.exp (-γ/2*(j:ℝ)) := by
  have hA0 : 0<A := lt_of_lt_of_le zero_lt_one hA
  rw [←Real.exp_log hA0] at hA ⊢
  rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : 4*(2*γ+Real.log A)*(n:ℝ) ≤ γ*(j:ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hnj hγ.le)
    field_simp at h
    nlinarith
  nlinarith
/-- Exponential coefficient decay from bounds at consecutive sample points. -/
lemma exponential_polynomial_sample_tail {q : ℝ} (hq0 : 0<q) (hq1 : q<1) :
    ∃ D γ : ℝ,0<D ∧ 0<γ ∧ ∀ N : ℕ,0<N → ∀ P : Polynomial ℝ,P.natDegree<N →
      (∀ i : Fin N,|P.eval (N+(i:ℝ))| ≤ (q^ (2*N))⁻¹) →
      ∀ j : ℕ,(D*(N:ℝ) ≤ j) → |q^j*P.eval (j:ℝ)| ≤ Real.exp (-γ*(j:ℝ)) := by
  let γ := -Real.log q
  have hγ : 0<γ := neg_pos.mpr (Real.log_neg hq0 hq1)
  let A := max 1 (8/γ)
  let D := max 2 (4*(2*γ+Real.log A)/γ)
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0<A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨D,γ/2,lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _),by positivity,?_⟩
  intro N hN P hP hvalues j hj
  have hnj : 2*(N:ℝ) ≤ j := le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hj
  have hn : N-1+1=N := by omega
  have hx : (N:ℝ)+(N-1:ℕ) ≤ j := by
    have h : ((N-1:ℕ):ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    linarith
  have hbound := integer_polynomial_exponential_bound (N-1) (N:ℝ) (j:ℝ) ((q^(2*N))⁻¹) (γ/4)
    (by positivity) hx (by positivity) (by positivity) P (by omega)
    (fun i=>by simpa only [hn,Fin.val_cast] using hvalues (Fin.cast hn i))
  have hr : (2/(γ/4))^(N-1) ≤ A^N := by
    apply (pow_le_pow_left₀ (by positivity) (show 2/(γ/4) ≤ A by rw [show 2/(γ/4)=8/γ by ring];exact le_max_right _ _) _).trans
    exact pow_le_pow_right₀ hA (Nat.sub_le _ _)
  have hqj : q^j=Real.exp (-γ*(j:ℝ)) := by
    rw [show -γ*(j:ℝ)=(j:ℝ)*Real.log q by dsimp [γ];ring,Real.exp_nat_mul,Real.exp_log hq0]
  have hqN : (q^(2*N))⁻¹=Real.exp (2*γ*(N:ℝ)) := by
    rw [show 2*γ*(N:ℝ)=-((2*N:ℕ):ℝ)*Real.log q by dsimp [γ];push_cast;ring,
      neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hq0]
  rw [abs_mul,abs_of_pos (pow_pos hq0 _),hqj]
  calc
    _ ≤ Real.exp (-γ*(j:ℝ))*(((q^(2*N))⁻¹)*(2/(γ/4))^(N-1)*Real.exp (γ/4*(j:ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ Real.exp (-γ*(j:ℝ))*(((q^(2*N))⁻¹)*A^N*Real.exp (γ/4*(j:ℝ))) := by gcongr
    _ = Real.exp (-γ*(j:ℝ))*Real.exp (2*γ*(N:ℝ))*A^N*Real.exp (γ/4*(j:ℝ)) := by rw [hqN];ring
    _ ≤ _ := by
      simpa only [neg_div] using exp_power_bound A γ hA hγ N j
        (le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hj)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
/-- The uniform coefficient decay asserted in the approximation paragraph,
for the literal complete zero/L² jet space and the explicit sech weight. -/
lemma completeJetSech_exponential_coefficients {u : ℝ} (hu : |u|<1) (hu0 : u≠0) :
    ∃ D γ : ℝ,0<D ∧ 0<γ ∧ ∀ N:ℕ,0<N → ∀ a c:Fin N→ℝ,
      symmetricSechPair (completeJetCombination N ((2*Real.arctan u)^2) a c)
        (completeJetCombination N ((2*Real.arctan u)^2) a c)≤1 →
      ∀ j:ℕ,D*(N:ℝ)≤j →
        |symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) (completeJetCombination N ((2*Real.arctan u)^2) a c)|≤
          Real.exp (-γ*(j:ℝ)) := by
  let q:=u^2
  have hq0:0<q:=sq_pos_of_ne_zero hu0
  have hq1:q<1:=by have:=abs_lt.mp hu;dsimp [q];nlinarith
  obtain ⟨D,γ,hD,hγ,hdecay⟩:=exponential_polynomial_sample_tail hq0 hq1
  obtain ⟨δ,hd,hlim⟩:=arctan_label_margin hu
  refine ⟨max 1 D,γ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hγ,?_⟩
  intro N hN a c hnorm j hj
  let f:=completeJetCombination N ((2*Real.arctan u)^2) a c
  have hff:=completeJetSech_norm_integrable (sq_nonneg (2*Real.arctan u)) hd hlim N a c
  have hf:=completeJetSech_pair_integrable (sq_nonneg (2*Real.arctan u)) hd hlim N a c
  obtain ⟨P,hP,hcoef⟩:=completeJetCombination_coefficient hu hu0 N hN a c
  have hsample (i:Fin N) : |P.eval ((N:ℝ)+(i:ℝ))|≤(q^(2*N))⁻¹ := by
    have hc:=evenProjection_coefficient_le_one f hff (fun j=>hf (2*j)) hnorm (N+i)
    dsimp [f] at hc
    rw [hcoef (N+i) (by omega),abs_mul,abs_of_pos (pow_pos hq0 _)] at hc
    have hp : q^(2*N)≤q^(N+(i:ℕ)) := pow_le_pow_of_le_one hq0.le hq1.le (by have:=i.isLt;omega)
    have htmp:=mul_le_mul_of_nonneg_right hp (abs_nonneg (P.eval ((N+i:ℕ):ℝ)))
    have hconc: q^(2*N)*|P.eval ((N+i:ℕ):ℝ)|≤1:=htmp.trans hc
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hq0 _)).mpr
    simpa only [Nat.cast_add,mul_comm] using hconc
  have hNj:N≤j := by
    have hh:=le_trans (mul_le_mul_of_nonneg_right (le_max_left 1 D) (by positivity : 0≤(N:ℝ))) hj
    simp only [one_mul] at hh
    exact_mod_cast hh
  rw [hcoef j hNj]
  exact hdecay N hN P hP hsample j
    ((mul_le_mul_of_nonneg_right (le_max_right 1 D) (by positivity)).trans hj)
lemma completeJetSech_projection_approximation {u : ℝ} (hu : |u|<1) (hu0 : u≠0) :
    ∃ D γ : ℝ,0<D ∧ 0<γ ∧ ∀ N:ℕ,0<N → ∀ a c:Fin N→ℝ,
      symmetricSechPair (completeJetCombination N ((2*Real.arctan u)^2) a c)
        (completeJetCombination N ((2*Real.arctan u)^2) a c)≤1 →
      ∀ K:ℕ,D*(N:ℝ)≤K →
        let f:=completeJetCombination N ((2*Real.arctan u)^2) a c
        symmetricSechPair (fun p=>f p-evenPollaczekFinite K (fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f) p)
          (fun p=>f p-evenPollaczekFinite K (fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f) p) ≤
            Real.exp (-2*γ*(K:ℝ))/(1-Real.exp (-2*γ)) := by
  obtain ⟨D,γ,hD,hγ,hc⟩:=completeJetSech_exponential_coefficients hu hu0
  obtain ⟨δ,hd,hlim⟩:=arctan_label_margin hu
  refine ⟨D,γ,hD,hγ,?_⟩
  intro N hN a c hnorm K hK
  apply evenProjection_exponential_error _
    (completeJetSech_norm_integrable (sq_nonneg _) hd hlim N a c)
    (fun j=>completeJetSech_pair_integrable (sq_nonneg _) hd hlim N a c (2*j))
    (completeJetSech_parseval_residual (sq_nonneg _) hd hlim N a c) hγ K
  intro j hj
  exact hc N hN a c hnorm j (hK.trans (by exact_mod_cast hj))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma cosineKernelJet_scale_right (r : ℕ) (b d x : ℝ) :
    cosineKernelJet r 0 b (d*x)=d^r*cosineKernelJet r 0 (d*b) x := by
  unfold cosineKernelJet
  rw [←tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [kernelJetTerm,polynomialJet_X_pow,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,mul_pow]
  by_cases hr:r≤k
  · have he:d^r*d^(k-r)=d^k:=by rw [←pow_add,Nat.add_sub_of_le hr]
    calc
      _ = ((k.choose r:ℕ):ℝ)*b^(k-r)*(d^r*d^(k-r))*x^k/(2*k).factorial := by rw [he];ring
      _ = _ := by ring
  · simp only [Nat.choose_eq_zero_of_lt (by omega : k<r),Nat.cast_zero,zero_mul,zero_div,mul_zero]
lemma completeJetCombination_scale (N : ℕ) (b s : ℝ) (a c : Fin N→ℝ) (p : ℝ) :
    completeJetCombination N b a c (s*p)=
      completeJetCombination N (s^2*b) (fun i=>a i*(s^2)^(i:ℕ)) (fun i=>c i*(s^2)^(i:ℕ)) p := by
  unfold completeJetCombination
  simp only [mul_pow,cosineKernelJet_scale_right,mul_zero]
  congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
lemma twoJetCombination_split (N:ℕ) (a:Fin (2*N)→ℝ) :
    ∃ b c:Fin N→ℝ,∀ p:ℝ,twoJetCombination N a (p^2)=completeJetCombination N (angle^2) b c p := by
  have hn:2*N=N+N:=by omega
  let v:Fin (N+N)→ℝ:=fun i=>a (Fin.cast hn.symm i)
  refine ⟨fun i=>v (Fin.castAdd N i),fun i=>v (Fin.natAdd N i),?_⟩
  intro p
  have hsum:twoJetCombination N a (p^2)=
    ∑ i:Fin (N+N),v i*cosineKernelJet (nodalOrder (twoKnotLabels N) i) 0 (twoKnotLabels N i) (p^2) := by
    unfold twoJetCombination
    exact Fintype.sum_equiv (finCongr hn) _ _ (fun i=>by simp [v])
  rw [hsum,Fin.sum_univ_add]
  unfold completeJetCombination
  congr 1
  · apply sum_congr rfl
    intro i _
    simp only [Fin.val_castAdd,twoKnot_nodalOrder,twoKnotLabels,ite_eq_left i.isLt]
  · apply sum_congr rfl
    intro i _
    simp only [Fin.val_natAdd,twoKnot_nodalOrder,twoKnotLabels,show ¬N+(i:ℕ)<N by omega,ite_false,Nat.add_sub_cancel_left]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter Topology
lemma sum_fin_geometric_le {r : ℝ} (hr : 2≤r) (K : ℕ) :
    (∑ j:Fin K,r^(j:ℕ))≤r^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    calc
      (∑ j:Fin K,r^(j:ℕ))+r^K ≤ r^K+r^K := by linarith
      _ ≤ r^K*r := by nlinarith [pow_nonneg (by linarith : 0≤r) K]
      _ = r^(K+1) := (pow_succ _ _).symm

lemma evenFinite_pointwise_bound (K : ℕ) (a : Fin K→ℝ) (ha : ∑ j,(a j)^2≤1) (p : ℝ) :
    (evenPollaczekFinite K a p)^2≤
      ((1-(1/4:ℝ)^2)^(-(1:ℝ)/2))^2*256^K*Real.exp (4*Real.artanh (1/4)*|p|) := by
  let C:ℝ:=(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)
  have hC:0<C:=by dsimp [C];positivity
  have hQ (j:Fin K) : (pollaczekCoeff p (2*j))^2≤C^2*256^(j:ℕ)*Real.exp (4*Real.artanh (1/4)*|p|) := by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) (pollaczekCoeff_exp_bound (2*j) p) 2
    simp only [sq_abs] at hh
    refine hh.trans_eq ?_
    change (4^(2*(j:ℕ))*C*Real.exp (2*Real.artanh (1/4)*|p|))^2=_
    rw [mul_pow,mul_pow,←Real.exp_nat_mul]
    have hpw : ((4:ℝ)^(2*(j:ℕ)))^2=256^(j:ℕ) := by
      rw [←pow_mul,show (2*(j:ℕ))*2=4*(j:ℕ) by omega,pow_mul]
      norm_num
    rw [hpw]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(2*Real.artanh (1/4)*|p|)=4*Real.artanh (1/4)*|p| by ring]
    ring
  have hs:=sum_mul_sq_le_sq_mul_sq univ a (fun j=>pollaczekCoeff p (2*j))
  change (evenPollaczekFinite K a p)^2≤(∑ j,(a j)^2)*(∑ j:Fin K,(pollaczekCoeff p (2*j))^2) at hs
  calc
    _ ≤ (∑ j,(a j)^2)*(∑ j:Fin K,(pollaczekCoeff p (2*j))^2) := hs
    _ ≤ ∑ j:Fin K,(pollaczekCoeff p (2*j))^2 := by
      simpa using mul_le_mul_of_nonneg_right ha (sum_nonneg (fun j _=>sq_nonneg _))
    _ ≤ ∑ j:Fin K,C^2*256^(j:ℕ)*Real.exp (4*Real.artanh (1/4)*|p|) := sum_le_sum (fun j _=>hQ j)
    _ = C^2*(∑ j:Fin K,(256:ℝ)^(j:ℕ))*Real.exp (4*Real.artanh (1/4)*|p|) := by rw [←sum_mul,←mul_sum]
    _ ≤ _ := by gcongr;exact sum_fin_geometric_le (by norm_num) K
lemma evenFinite_spatial_tail (K : ℕ) (a : Fin K→ℝ) (ha : ∑ j,(a j)^2≤1) {R : ℝ} (hR : 0≤R) :
    (∫ p in Set.Ioi R,sechPairIntegrand (evenPollaczekFinite K a) (evenPollaczekFinite K a) p) ≤
      (4*((1-(1/4:ℝ)^2)^(-(1:ℝ)/2))^2*256^K)*
        (Real.exp ((4*Real.artanh (1/4)-Real.pi)*R)/(Real.pi-4*Real.artanh (1/4))) := by
  let C:ℝ:=(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)
  let d:ℝ:=4*Real.artanh (1/4)-Real.pi
  have hd:d<0:=by dsimp [d];linarith [quarter_artanh_bounds.2]
  have hi:IntegrableOn (fun p=>(4*C^2*256^K)*Real.exp (d*p)) (Set.Ioi R):=
    (integrableOn_exp_mul_Ioi hd R).const_mul _
  have hleft:= (evenFinite_square_integrable K a).mono_set (Set.Ioi_subset_Ioi hR)
  calc
    _ ≤ ∫ p in Set.Ioi R,(4*C^2*256^K)*Real.exp (d*p) := by
      apply integral_mono_ae hleft hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      have hp0:0≤p:=hR.trans hp.le
      have h1:=evenFinite_pointwise_bound K a ha p
      have h2:=evenFinite_pointwise_bound K a ha (-p)
      simp only [abs_neg,abs_of_nonneg hp0] at h1 h2
      have hc:Real.exp (Real.pi*p)/2≤Real.cosh (Real.pi*p):=by
        rw [Real.cosh_eq];linarith [Real.exp_pos (-(Real.pi*p))]
      unfold sechPairIntegrand
      calc
        _ ≤ (2*C^2*256^K*Real.exp (4*Real.artanh (1/4)*p))/Real.cosh (Real.pi*p) := by
          apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
          dsimp [C] at *
          nlinarith
        _ ≤ (2*C^2*256^K*Real.exp (4*Real.artanh (1/4)*p))/(Real.exp (Real.pi*p)/2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hc
        _ = _ := by dsimp [d];rw [sub_mul,Real.exp_sub];ring
    _ = _ := by
      rw [integral_const_mul,integral_exp_mul_Ioi hd]
      dsimp [C,d]
      rw [show Real.pi-4*Real.artanh (1/4)=-(4*Real.artanh (1/4)-Real.pi) by ring,div_neg]
      ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory
lemma sechPairIntegrand_self_nonneg (f : ℝ→ℝ) (p:ℝ) : 0≤ sechPairIntegrand f f p := by
  unfold sechPairIntegrand
  exact div_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Real.cosh_pos _).le
lemma sechPair_difference_integrable (f g:ℝ→ℝ)
    (hf:IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hg:IntegrableOn (sechPairIntegrand g g) (Set.Ioi 0))
    (hfg:IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0)) :
    IntegrableOn (sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p)) (Set.Ioi 0) := by
  have he:sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p)=
      fun p=>sechPairIntegrand f f p-2*sechPairIntegrand f g p+sechPairIntegrand g g p := by
    funext p;unfold sechPairIntegrand;ring
  rw [he]
  exact (hf.sub (hfg.const_mul 2)).add hg
lemma sech_local_mass (f g:ℝ→ℝ)
    (hf:IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hg:IntegrableOn (sechPairIntegrand g g) (Set.Ioi 0))
    (hfg:IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0))
    (hn:symmetricSechPair f f=1) {R:ℝ} (hR:0≤R)
    (he:symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p)≤1/8)
    (ht:(∫ p in Set.Ioi R,sechPairIntegrand g g p)≤1/8) :
    1/2≤∫ p in Set.Ioc 0 R,sechPairIntegrand f f p := by
  have hd:=sechPair_difference_integrable f g hf hg hfg
  have hsub:Set.Ioi R⊆Set.Ioi (0:ℝ):=Set.Ioi_subset_Ioi hR
  have hdtail:(∫ p in Set.Ioi R,sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p) p)≤
      symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p) := by
    apply setIntegral_mono_set hd
    · exact Filter.Eventually.of_forall (sechPairIntegrand_self_nonneg _)
    · exact Filter.Eventually.of_forall hsub
  have htail:(∫ p in Set.Ioi R,sechPairIntegrand f f p)≤1/2 := by
    calc
      _ ≤ ∫ p in Set.Ioi R,2*sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p) p+2*sechPairIntegrand g g p := by
        apply integral_mono_ae (hf.mono_set hsub) (((hd.mono_set hsub).const_mul 2).add ((hg.mono_set hsub).const_mul 2))
        filter_upwards with p
        change (f p*f p+f (-p)*f (-p))/Real.cosh (Real.pi*p) ≤
          2*(((f p-g p)*(f p-g p)+(f (-p)-g (-p))*(f (-p)-g (-p)))/Real.cosh (Real.pi*p))+
          2*((g p*g p+g (-p)*g (-p))/Real.cosh (Real.pi*p))
        have hc:=Real.cosh_pos (Real.pi*p)
        rw [←mul_div_assoc,←mul_div_assoc,←add_div]
        apply (div_le_div_iff_of_pos_right hc).mpr
        nlinarith [sq_nonneg (f p-2*g p),sq_nonneg (f (-p)-2*g (-p))]
      _ = 2*(∫ p in Set.Ioi R,sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p) p)+2*(∫ p in Set.Ioi R,sechPairIntegrand g g p) := by
        rw [integral_add ((hd.mono_set hsub).const_mul _) ((hg.mono_set hsub).const_mul _),integral_const_mul,integral_const_mul]
      _ ≤ _ := by linarith
  have hsum:(∫ p in Set.Ioc 0 R,sechPairIntegrand f f p)+(∫ p in Set.Ioi R,sechPairIntegrand f f p)=1 := by
    rw [←setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi (hf.mono_set Set.Ioc_subset_Ioi_self) (hf.mono_set hsub),Set.Ioc_union_Ioi_eq_Ioi hR]
    exact hn
  linarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real
lemma exponential_nat_uniform_small {r B:ℝ} (hr:0<r) (hB:0<B) (D:ℝ) :
    ∃ J:ℕ,0<J ∧ D≤J ∧ ∀ N:ℕ,0<N → B*Real.exp (-r*((J*N:ℕ):ℝ))≤1/8 := by
  obtain ⟨J,hJ⟩:=exists_nat_gt (max 1 (max D ((|Real.log (8*B)|+1)/r)))
  have hJ1:(1:ℝ)<J:=lt_of_le_of_lt (le_max_left _ _) hJ
  have hJD:D<J:=lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hJ
  have hJr:(|Real.log (8*B)|+1)/r<(J:ℝ):=lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hJ
  have hprod : |Real.log (8*B)|+1<r*(J:ℝ) := by
    have hh:=(div_lt_iff₀ hr).mp hJr
    nlinarith
  refine ⟨J,by exact_mod_cast (lt_trans zero_lt_one hJ1),hJD.le,?_⟩
  intro N hN
  have hN1:(1:ℝ)≤N:=by exact_mod_cast hN
  have hmul:=mul_le_mul_of_nonneg_left hN1 (show 0≤r*(J:ℝ) by positivity)
  have he : -r*((J*N:ℕ):ℝ)≤ -Real.log (8*B) := by
    simp only [Nat.cast_mul]
    nlinarith [le_abs_self (Real.log (8*B))]
  calc
    _ ≤ B*Real.exp (-Real.log (8*B)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB.le
    _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)];field_simp
lemma spatial_exponential_constant {B lam:ℝ} (hB:0<B) (hlam:0<lam) (J:ℕ) :
    ∃ R:ℝ,0<R ∧ ∀ N:ℕ,0<N →
      B*256^(J*N)*Real.exp (-lam*(R*(N:ℝ)))≤1/8 := by
  let t:=|Real.log (8*B)|+1
  let R:=((J:ℝ)*Real.log 256+t)/lam
  have ht:0<t:=by dsimp [t];positivity
  have hlog:0<Real.log 256:=Real.log_pos (by norm_num)
  have hR:0<R:=by dsimp [R];positivity
  refine ⟨R,hR,?_⟩
  intro N hN
  have heq : (256:ℝ)^(J*N)*Real.exp (-lam*(R*(N:ℝ)))=Real.exp (-t*(N:ℝ)) := by
    rw [show (256:ℝ)^(J*N)=Real.exp (((J*N:ℕ):ℝ)*Real.log 256) by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)],←Real.exp_add]
    congr 1
    dsimp [R]
    simp only [Nat.cast_mul]
    field_simp
    ring
  rw [mul_assoc,heq]
  have hN1:(1:ℝ)≤N:=by exact_mod_cast hN
  have he:-t*(N:ℝ)≤ -Real.log (8*B) := by
    have hh:=mul_le_mul_of_nonneg_left hN1 ht.le
    dsimp [t] at hh ⊢
    linarith [le_abs_self (Real.log (8*B))]
  calc
    _ ≤ B*Real.exp (-Real.log (8*B)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB.le
    _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)];field_simp
lemma exponential_relative_constant {r B b:ℝ} (hr:0<r) (hB:0<B) (hb:0<b) (D t:ℝ) :
    ∃ J:ℕ,0<J ∧ D≤J ∧ ∀ N:ℕ,0<N →
      B*Real.exp (-r*((J*N:ℕ):ℝ))≤b*Real.exp (-t*(N:ℝ)) := by
  obtain ⟨J,hJ⟩:=exists_nat_gt (max 1 (max D ((t+|Real.log (B/b)|+1)/r)))
  have hJ1:(1:ℝ)<J:=lt_of_le_of_lt (le_max_left _ _) hJ
  have hJD:D<J:=lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hJ
  have hJr:(t+|Real.log (B/b)|+1)/r<(J:ℝ):=lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hJ
  have hprod:t+|Real.log (B/b)|+1<r*(J:ℝ):=by
    have hh:=(div_lt_iff₀ hr).mp hJr;nlinarith
  refine ⟨J,by exact_mod_cast (lt_trans zero_lt_one hJ1),hJD.le,?_⟩
  intro N hN
  have hN1:(1:ℝ)≤N:=by exact_mod_cast hN
  have hm:=mul_le_mul_of_nonneg_left hN1 (show 0≤r*(J:ℝ)-t by linarith [abs_nonneg (Real.log (B/b))])
  have hex:-r*((J*N:ℕ):ℝ)≤-t*(N:ℝ)-Real.log (B/b):=by
    simp only [Nat.cast_mul]
    nlinarith [le_abs_self (Real.log (B/b))]
  calc
    _ ≤ B*Real.exp (-t*(N:ℝ)-Real.log (B/b)):=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hB.le
    _ = _ := by rw [Real.exp_sub,Real.exp_log (div_pos hB hb)];field_simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
lemma completeJetSech_concentration {u:ℝ} (hu:|u|<1) (hu0:u≠0) :
    ∃ R:ℝ,0<R ∧ ∀ N:ℕ,0<N → ∀ a c:Fin N→ℝ,
      symmetricSechPair (completeJetCombination N ((2*Real.arctan u)^2) a c)
        (completeJetCombination N ((2*Real.arctan u)^2) a c)=1 →
      1/2≤∫ p in Set.Ioc 0 (R*(N:ℝ)),
        sechPairIntegrand (completeJetCombination N ((2*Real.arctan u)^2) a c)
          (completeJetCombination N ((2*Real.arctan u)^2) a c) p := by
  obtain ⟨D,γ,hD,hγ,happ⟩:=completeJetSech_projection_approximation hu hu0
  have hden:0<1-Real.exp (-2*γ):=by have:=Real.exp_lt_one_iff.mpr (by linarith : -2*γ<0);linarith
  obtain ⟨J,hJ,hJD,hsmall⟩:=exponential_nat_uniform_small (by positivity : 0<2*γ) (by positivity : 0<(1-Real.exp (-2*γ))⁻¹) D
  let C:ℝ:=(1-(1/4:ℝ)^2)^(-(1:ℝ)/2)
  let lam:ℝ:=Real.pi-4*Real.artanh (1/4)
  have hC:0<C:=by dsimp [C];positivity
  have hlam:0<lam:=by dsimp [lam];linarith [quarter_artanh_bounds.2]
  obtain ⟨R,hR,hspatial⟩:=spatial_exponential_constant (by positivity : 0<4*C^2/lam) hlam J
  refine ⟨R,hR,?_⟩
  intro N hN a c hnorm
  let f:=completeJetCombination N ((2*Real.arctan u)^2) a c
  let v:Fin (J*N)→ℝ:=fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f
  let g:=evenPollaczekFinite (J*N) v
  obtain ⟨δ,hd,hlim⟩:=arctan_label_margin hu
  have hff:=completeJetSech_norm_integrable (sq_nonneg _) hd hlim N a c
  have hfp:=completeJetSech_pair_integrable (sq_nonneg _) hd hlim N a c
  have hcoef : (∑ j:Fin (J*N),(v j)^2)≤1:=by
    have hh:=even_projection_bessel (J*N) f hff (fun j=>hfp (2*j))
    change 0≤ symmetricSechPair f f-∑ j:Fin (J*N),(v j)^2 at hh
    change symmetricSechPair f f=1 at hnorm
    linarith
  have herror:symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p)≤1/8 := by
    have hK:D*(N:ℝ)≤((J*N:ℕ):ℝ):=by simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_right hJD (by positivity : 0≤(N:ℝ))
    have hh:=happ N hN a c hnorm.le (J*N) hK
    change symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p)≤_ at hh
    have hhsmall := hsmall N hN
    rw [show -(2*γ)= -2*γ by ring] at hhsmall
    exact hh.trans (by simpa only [div_eq_mul_inv,mul_comm] using hhsmall)
  have htail:(∫ p in Set.Ioi (R*(N:ℝ)),sechPairIntegrand g g p)≤1/8 := by
    have hh:=evenFinite_spatial_tail (J*N) v hcoef (R:=R*(N:ℝ)) (by positivity)
    change (∫ p in Set.Ioi (R*(N:ℝ)),sechPairIntegrand g g p)≤_ at hh
    convert hh.trans (le_of_eq_of_le (by dsimp [lam]; rw [show (4*Real.artanh (1/4)-Real.pi)*(R*(N:ℝ))=-(Real.pi-4*Real.artanh (1/4))*(R*(N:ℝ)) by ring]; ring : (4*C^2*256^(J*N))*(Real.exp ((4*Real.artanh (1/4)-Real.pi)*(R*(N:ℝ)))/lam)=
      (4*C^2/lam)*256^(J*N)*Real.exp (-lam*(R*(N:ℝ)))) (hspatial N hN)) using 1
  exact sech_local_mass f g hff (evenFinite_square_integrable _ v)
    (by rw [sechPairIntegrand_comm];exact evenFinite_pair_integrable _ v f (fun j=>hfp (2*j))) hnorm (by positivity) herror htail
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter
noncomputable def weightedHalfNorm (w f:ℝ→ℝ):ℝ:=∫ p in Set.Ioi 0,(f p)^2*w p
lemma sechPairIntegrand_even {f:ℝ→ℝ} (he:∀ p,f (-p)=f p) (p:ℝ) :
    sechPairIntegrand f f p=2*(f p)^2/Real.cosh (Real.pi*p) := by
  unfold sechPairIntegrand;rw [he];ring
lemma weightedHalf_integrable {w f:ℝ→ℝ} {A:ℝ}
    (hw:Measurable w) (hf:Measurable f) (he:∀ p,f (-p)=f p)
    (hwn:∀ p,0<p → 0≤w p) (hwu:∀ p,0<p → w p≤A/Real.cosh (Real.pi*p))
    (hff:IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0)) :
    IntegrableOn (fun p=>(f p)^2*w p) (Set.Ioi 0) := by
  apply (hff.const_mul (A/2)).mono' ((hf.pow_const 2).mul hw).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (hwn p hp)),sechPairIntegrand_even he]
  calc
    _ ≤ (f p)^2*(A/Real.cosh (Real.pi*p)):=mul_le_mul_of_nonneg_left (hwu p hp) (sq_nonneg _)
    _ = _ := by ring
lemma weightedHalf_le_sech {w f:ℝ→ℝ} {A:ℝ}
    (hw:Measurable w) (hf:Measurable f) (he:∀ p,f (-p)=f p)
    (hwn:∀ p,0<p → 0≤w p) (hwu:∀ p,0<p → w p≤A/Real.cosh (Real.pi*p))
    (hff:IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0)) :
    weightedHalfNorm w f≤(A/2)*symmetricSechPair f f := by
  unfold weightedHalfNorm symmetricSechPair
  rw [←integral_const_mul]
  apply integral_mono_ae (weightedHalf_integrable hw hf he hwn hwu hff) (hff.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [sechPairIntegrand_even he]
  calc
    _ ≤ (f p)^2*(A/Real.cosh (Real.pi*p)):=mul_le_mul_of_nonneg_left (hwu p hp) (sq_nonneg _)
    _ = _ := by ring
lemma weightedHalf_lower_local {w f:ℝ→ℝ} {a R:ℝ} (ha:0<a)
    (he:∀ p,f (-p)=f p) (hwn:∀ p,0<p → 0≤w p)
    (hwl:∀ p,0<p → p≤R → a/Real.cosh (Real.pi*p)≤w p)
    (hf:IntegrableOn (sechPairIntegrand f f) (Set.Ioi 0))
    (hfw:IntegrableOn (fun p=>(f p)^2*w p) (Set.Ioi 0))
    (hloc:1/2≤∫ p in Set.Ioc 0 R,sechPairIntegrand f f p) :
    a/4≤weightedHalfNorm w f := by
  have hlocw:(a/2)*(∫ p in Set.Ioc 0 R,sechPairIntegrand f f p)≤∫ p in Set.Ioc 0 R,(f p)^2*w p := by
    rw [←integral_const_mul]
    apply integral_mono_ae ((hf.mono_set Set.Ioc_subset_Ioi_self).const_mul _) (hfw.mono_set Set.Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
    rw [sechPairIntegrand_even he]
    calc
      _ = (f p)^2*(a/Real.cosh (Real.pi*p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hwl p hp.1 hp.2) (sq_nonneg _)
  have hbig:(∫ p in Set.Ioc 0 R,(f p)^2*w p)≤weightedHalfNorm w f := by
    apply setIntegral_mono_set hfw
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      exact mul_nonneg (sq_nonneg _) (hwn p hp)
    · exact Eventually.of_forall Set.Ioc_subset_Ioi_self
  have hh:=mul_le_mul_of_nonneg_left hloc (show 0≤a/2 by positivity)
  nlinarith
lemma scaledStripDensity_measurable (s:ℝ) : Measurable (scaledStripDensity s) := by
  unfold scaledStripDensity stripDensity
  fun_prop
lemma scaledStripDensity_pos {s p:ℝ} (hs:0<s) (hp:0<p) : 0<scaledStripDensity s p := by
  unfold scaledStripDensity
  exact mul_pos hs (stripDensity_pos (mul_pos hs hp))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
lemma completeJetCombination_continuous (N:ℕ) (b:ℝ) (a c:Fin N→ℝ) :
    Continuous (completeJetCombination N b a c) := by
  have hc (r:ℕ) (b:ℝ):Continuous (fun p=>cosineKernelJet r 0 b (p^2)):=
    (continuous_iff_continuousAt.mpr (fun x=>(cosineKernelJet_hasDerivAt_right r 0 b x).continuousAt)).comp (continuous_id.pow 2)
  unfold completeJetCombination
  exact (continuous_finsetSum _ (fun (i:Fin N) _=>(hc (i:ℕ) 0).const_mul (a i))).add
    (continuous_finsetSum _ (fun (i:Fin N) _=>(hc (i:ℕ) b).const_mul (c i)))
lemma completeJetCombination_even (N:ℕ) (b:ℝ) (a c:Fin N→ℝ) (p:ℝ) :
    completeJetCombination N b a c (-p)=completeJetCombination N b a c p := by
  simp only [completeJetCombination,neg_sq]
lemma completeJetCombination_smul (N:ℕ) (b d:ℝ) (a c:Fin N→ℝ) :
    completeJetCombination N b (fun i=>d*a i) (fun i=>d*c i)=fun p=>d*completeJetCombination N b a c p := by
  funext p
  simp only [completeJetCombination,mul_assoc,←mul_sum,←mul_add]
lemma evenFinite_continuous (K:ℕ) (v:Fin K→ℝ):Continuous (evenPollaczekFinite K v) := by
  have he:evenPollaczekFinite K v=fun p=>(∑ j,v j • evenPoly (-1) j).eval (p^2):=funext (evenPollaczekFinite_polynomial K v)
  rw [he]
  exact (∑ j,v j • evenPoly (-1) j).continuous.comp (continuous_id.pow 2)
lemma evenFinite_even (K:ℕ) (v:Fin K→ℝ) (p:ℝ) : evenPollaczekFinite K v (-p)=evenPollaczekFinite K v p := by
  rw [evenPollaczekFinite_polynomial,evenPollaczekFinite_polynomial,neg_sq]
lemma evenFinite_polynomial_degree {K:ℕ} (hK:0<K) (v:Fin K→ℝ) :
    (∑ j,v j • evenPoly (-1) j).natDegree<K := by
  apply Nat.lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun j _=>?_) (Nat.sub_lt hK (by omega : 0<1))
  exact (natDegree_smul_le _ _).trans (by rw [(pollaczek_evenOdd_degree j).1];omega)
lemma symmetricSechPair_smul_both (f:ℝ→ℝ) (d:ℝ) :
    symmetricSechPair (fun p=>d*f p) (fun p=>d*f p)=d^2*symmetricSechPair f f := by
  rw [symmetricSechPair_smul_left,symmetricSechPair_comm,symmetricSechPair_smul_left,symmetricSechPair_comm]
  ring
lemma weightedHalfNorm_smul (w f:ℝ→ℝ) (d:ℝ) : weightedHalfNorm w (fun p=>d*f p)=d^2*weightedHalfNorm w f := by
  unfold weightedHalfNorm
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
lemma normalizedJetWeightedApproximation {u:ℝ} (hu:|u|<1) (hu0:u≠0)
    {w:ℝ→ℝ} (hw:Measurable w) (hwn:∀ p,0<p → 0≤w p)
    {A a β:ℝ} (hA:0<A) (ha:0<a)
    (hwu:∀ p,0<p → w p≤A/Real.cosh (Real.pi*p))
    (hwl:∀ R p:ℝ,0<p → p≤R → a*Real.exp (-β*R)/Real.cosh (Real.pi*p)≤w p) :
    ∃ J:ℕ,0<J ∧ ∀ N:ℕ,0<N → ∀ b c:Fin N→ℝ,
      symmetricSechPair (completeJetCombination N ((2*Real.arctan u)^2) b c)
        (completeJetCombination N ((2*Real.arctan u)^2) b c)=1 →
      ∃ P:Polynomial ℝ,P.natDegree<J*N ∧
        weightedHalfNorm w (fun p=>completeJetCombination N ((2*Real.arctan u)^2) b c p-P.eval (p^2))≤
          Real.exp (-2*(N:ℝ))*weightedHalfNorm w (completeJetCombination N ((2*Real.arctan u)^2) b c) := by
  obtain ⟨R,hR,hconc⟩:=completeJetSech_concentration hu hu0
  obtain ⟨D,γ,hD,hγ,happ⟩:=completeJetSech_projection_approximation hu hu0
  have hden:0<1-Real.exp (-2*γ):=by have:=Real.exp_lt_one_iff.mpr (by linarith : -2*γ<0);linarith
  obtain ⟨J,hJ,hJD,hsmall⟩:=exponential_relative_constant (by positivity : 0<2*γ)
    (by positivity : 0<(A/2)/(1-Real.exp (-2*γ))) (by positivity : 0<a/4) D (2+β*R)
  refine ⟨J,hJ,?_⟩
  intro N hN b c hnorm
  let f:=completeJetCombination N ((2*Real.arctan u)^2) b c
  let v:Fin (J*N)→ℝ:=fun j=>symmetricSechPair (fun p=>pollaczekCoeff p (2*j)) f
  let P:Polynomial ℝ:=∑ j,v j • evenPoly (-1) j
  let g:=evenPollaczekFinite (J*N) v
  have hgp (p:ℝ):g p=P.eval (p^2):=evenPollaczekFinite_polynomial _ _ _
  obtain ⟨δ,hd,hlim⟩:=arctan_label_margin hu
  have hff:=completeJetSech_norm_integrable (sq_nonneg _) hd hlim N b c
  have hfp:=completeJetSech_pair_integrable (sq_nonneg _) hd hlim N b c
  have hf:Measurable f:=(completeJetCombination_continuous _ _ _ _).measurable
  have hfe:∀ p,f (-p)=f p:=completeJetCombination_even _ _ _ _
  have hfw:=weightedHalf_integrable hw hf hfe hwn hwu hff
  have hlow:(a/4)*Real.exp (-β*(R*(N:ℝ)))≤weightedHalfNorm w f := by
    have hh:=weightedHalf_lower_local (by positivity : 0<a*Real.exp (-β*(R*(N:ℝ))))
      hfe hwn (hwl (R*(N:ℝ))) hff hfw (hconc N hN b c hnorm)
    convert hh using 1; ring
  have hfg:IntegrableOn (sechPairIntegrand f g) (Set.Ioi 0):=by
    rw [sechPairIntegrand_comm];exact evenFinite_pair_integrable _ v f (fun j=>hfp (2*j))
  have he:IntegrableOn (sechPairIntegrand (fun p=>f p-g p) (fun p=>f p-g p)) (Set.Ioi 0):=
    sechPair_difference_integrable f g hff (evenFinite_square_integrable _ v) hfg
  have hupper:=weightedHalf_le_sech hw (hf.sub (evenFinite_continuous _ v).measurable)
    (fun p=>by simp only [Pi.sub_apply,hfe,evenFinite_even]) hwn hwu he
  have hK:D*(N:ℝ)≤((J*N:ℕ):ℝ):=by simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_right hJD (by positivity : 0≤(N:ℝ))
  have herr:=happ N hN b c hnorm.le (J*N) hK
  change symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p)≤_ at herr
  refine ⟨P,evenFinite_polynomial_degree (Nat.mul_pos hJ hN) v,?_⟩
  change weightedHalfNorm w (fun p=>f p-P.eval (p^2))≤_
  rw [show (fun p=>f p-P.eval (p^2))=(fun p=>f p-g p) from funext (fun p=>by rw [hgp])]
  calc
    _ ≤ (A/2)*symmetricSechPair (fun p=>f p-g p) (fun p=>f p-g p):=hupper
    _ ≤ (A/2)*(Real.exp (-2*γ*((J*N:ℕ):ℝ))/(1-Real.exp (-2*γ))):=mul_le_mul_of_nonneg_left herr (by positivity)
    _ = ((A/2)/(1-Real.exp (-2*γ)))*Real.exp (-(2*γ)*((J*N:ℕ):ℝ)) := by rw [show -2*γ=-(2*γ) by ring];ring
    _ ≤ (a/4)*Real.exp (-(2+β*R)*(N:ℝ)):=hsmall N hN
    _ = Real.exp (-2*(N:ℝ))*((a/4)*Real.exp (-β*(R*(N:ℝ)))):=by
      rw [←mul_assoc,mul_comm (Real.exp _) (a/4),mul_assoc,←Real.exp_add]
      congr 2;ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset Filter
lemma weightedHalfNorm_nonneg {w:ℝ→ℝ} (hwn:∀ p,0<p → 0≤w p) (f:ℝ→ℝ) : 0≤weightedHalfNorm w f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact mul_nonneg (sq_nonneg _) (hwn p hp)
lemma relativeJetWeightedApproximation {u:ℝ} (hu:|u|<1) (hu0:u≠0)
    {w:ℝ→ℝ} (hw:Measurable w) (hwn:∀ p,0<p → 0≤w p)
    {A a β:ℝ} (hA:0<A) (ha:0<a)
    (hwu:∀ p,0<p → w p≤A/Real.cosh (Real.pi*p))
    (hwl:∀ R p:ℝ,0<p → p≤R → a*Real.exp (-β*R)/Real.cosh (Real.pi*p)≤w p) :
    ∃ J:ℕ,0<J ∧ ∀ N:ℕ,0<N → ∀ b c:Fin N→ℝ,
      ∃ P:Polynomial ℝ,P.natDegree<J*N ∧
        weightedHalfNorm w (fun p=>completeJetCombination N ((2*Real.arctan u)^2) b c p-P.eval (p^2))≤
          Real.exp (-2*(N:ℝ))*weightedHalfNorm w (completeJetCombination N ((2*Real.arctan u)^2) b c) := by
  obtain ⟨J,hJ,happ⟩:=normalizedJetWeightedApproximation hu hu0 hw hwn hA ha hwu hwl
  obtain ⟨δ,hd,hlim⟩:=arctan_label_margin hu
  refine ⟨J,hJ,?_⟩
  intro N hN b c
  let f:=completeJetCombination N ((2*Real.arctan u)^2) b c
  let S:=symmetricSechPair f f
  have hS0:0≤S:=symmetricSechPair_nonneg _
  by_cases hS:S=0
  · have hh:=weightedHalf_le_sech hw (completeJetCombination_continuous _ _ _ _).measurable
      (completeJetCombination_even _ _ _ _) hwn hwu
      (completeJetSech_norm_integrable (sq_nonneg _) hd hlim N b c)
    change weightedHalfNorm w f≤(A/2)*S at hh
    rw [hS,mul_zero] at hh
    have hnorm0:weightedHalfNorm w f=0:=le_antisymm hh (weightedHalfNorm_nonneg hwn f)
    refine ⟨0,by simpa using Nat.mul_pos hJ hN,?_⟩
    simp only [eval_zero,sub_zero]
    change weightedHalfNorm w f≤Real.exp (-2*(N:ℝ))*weightedHalfNorm w f
    rw [hnorm0,mul_zero]
  · have hSpos:0<S:=lt_of_le_of_ne hS0 (Ne.symm hS)
    let d:=Real.sqrt S
    have hdpos:0<d:=Real.sqrt_pos.mpr hSpos
    have hdsq:d^2=S:=Real.sq_sqrt hS0
    have hn:symmetricSechPair (completeJetCombination N ((2*Real.arctan u)^2) (fun i=>d⁻¹*b i) (fun i=>d⁻¹*c i))
        (completeJetCombination N ((2*Real.arctan u)^2) (fun i=>d⁻¹*b i) (fun i=>d⁻¹*c i))=1 := by
      rw [completeJetCombination_smul,symmetricSechPair_smul_both]
      change (d⁻¹)^2*S=1
      rw [←hdsq,←mul_pow,inv_mul_cancel₀ hdpos.ne',one_pow]
    obtain ⟨P,hP,herr⟩:=happ N hN (fun i=>d⁻¹*b i) (fun i=>d⁻¹*c i) hn
    rw [completeJetCombination_smul] at herr
    change weightedHalfNorm w (fun p=>d⁻¹*f p-P.eval (p^2))≤Real.exp (-2*(N:ℝ))*weightedHalfNorm w (fun p=>d⁻¹*f p) at herr
    refine ⟨d • P,(natDegree_smul_le _ _).trans_lt hP,?_⟩
    have heq:(fun p=>f p-(d • P).eval (p^2))=(fun p=>d*(d⁻¹*f p-P.eval (p^2))):=by
      funext p
      simp only [eval_smul,smul_eq_mul]
      rw [mul_sub,←mul_assoc,mul_inv_cancel₀ hdpos.ne',one_mul]
    change weightedHalfNorm w (fun p=>f p-(d • P).eval (p^2))≤_
    rw [heq,weightedHalfNorm_smul]
    have hh:=mul_le_mul_of_nonneg_left herr (sq_nonneg d)
    rw [weightedHalfNorm_smul] at hh
    rw [show d^2*(Real.exp (-2*(N:ℝ))*((d⁻¹)^2*weightedHalfNorm w f))=
      (d*d⁻¹)^2*(Real.exp (-2*(N:ℝ))*weightedHalfNorm w f) by ring,mul_inv_cancel₀ hdpos.ne',one_pow,one_mul] at hh
    exact hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial
lemma weightedHalfNorm_scale {s:ℝ} (hs:0<s) (f:ℝ→ℝ) :
    weightedHalfNorm (scaledStripDensity s) (fun p=>f (s*p))=weightedHalfNorm stripDensity f := by
  unfold weightedHalfNorm scaledStripDensity
  have he:(fun p=>(f (s*p))^2*(s*stripDensity (s*p)))=
      (fun p=>s*((f (s*p))^2*stripDensity (s*p))):=by funext p;ring
  rw [he,integral_const_mul]
  have ht:=integral_comp_mul_left_Ioi (fun p=>(f p)^2*stripDensity p) 0 hs
  simp only [mul_zero,smul_eq_mul] at ht
  rw [ht,←mul_assoc,mul_inv_cancel₀ hs.ne',one_mul]
lemma stripApproximation_scale_parameters :
    let s:ℝ:=16/5
    let u:ℝ:=Real.tan (Real.pi/5)
    0<s ∧ Real.pi<3*angle*s ∧ |u|<1 ∧ u≠0 ∧ s^2*angle^2=(2*Real.arctan u)^2 := by
  dsimp only
  have hp:0<Real.pi/5:=by positivity
  have hlt:Real.pi/5<Real.pi/2:=by linarith [Real.pi_pos]
  have ht:=Real.arctan_tan (by linarith [Real.pi_pos] : -(Real.pi/2)<Real.pi/5) hlt
  have hu:=Real.tan_pos_of_pos_of_lt_pi_div_two hp hlt
  refine ⟨by norm_num,?_,?_,hu.ne',?_⟩
  · unfold angle;linarith [Real.pi_pos]
  · rw [abs_of_pos hu]
    apply Real.arctan_strictMono.lt_iff_lt.mp
    rw [ht,Real.arctan_one]
    linarith [Real.pi_pos]
  · rw [ht];unfold angle;ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial Finset
lemma completeJetStripApproximation :
    ∃ J:ℕ,0<J ∧ ∀ N:ℕ,0<N → ∀ b c:Fin N→ℝ,
      ∃ P:Polynomial ℝ,P.natDegree<J*N ∧
        weightedHalfNorm stripDensity (fun p=>completeJetCombination N (angle^2) b c p-P.eval (p^2))≤
          Real.exp (-2*(N:ℝ))*weightedHalfNorm stripDensity (completeJetCombination N (angle^2) b c) := by
  let s:ℝ:=16/5
  let u:ℝ:=Real.tan (Real.pi/5)
  obtain ⟨hs,hsL,hu,hu0,hlabel⟩:=stripApproximation_scale_parameters
  change 0<s at hs
  change Real.pi<3*angle*s at hsL
  change |u|<1 at hu
  change u≠0 at hu0
  change s^2*angle^2=(2*Real.arctan u)^2 at hlabel
  obtain ⟨A,a,β,hA,ha,_,hwu,hwl⟩:=scaledStripDensity_sech_bounds hs hsL
  obtain ⟨J,hJ,happ⟩:=relativeJetWeightedApproximation hu hu0 (scaledStripDensity_measurable s)
    (fun p hp=>(scaledStripDensity_pos hs hp).le) hA ha hwu hwl
  refine ⟨J,hJ,?_⟩
  intro N hN b c
  let B:Fin N→ℝ:=fun i=>b i*(s^2)^(i:ℕ)
  let C:Fin N→ℝ:=fun i=>c i*(s^2)^(i:ℕ)
  obtain ⟨P,hP,herr⟩:=happ N hN B C
  let Q:=polynomialDilate (s^2)⁻¹ P
  have hscale (p:ℝ):completeJetCombination N (angle^2) b c (s*p)=
      completeJetCombination N ((2*Real.arctan u)^2) B C p := by
    rw [completeJetCombination_scale,hlabel]
  have hQ (p:ℝ):Q.eval ((s*p)^2)=P.eval (p^2) := by
    rw [polynomialDilate_eval,mul_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hs.ne'),one_mul]
  refine ⟨Q,(polynomialDilate_degree _ P).trans_lt hP,?_⟩
  rw [←weightedHalfNorm_scale hs (fun p=>completeJetCombination N (angle^2) b c p-Q.eval (p^2)),
    ←weightedHalfNorm_scale hs (completeJetCombination N (angle^2) b c)]
  simp_rw [hscale,hQ]
  exact herr
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial
/-- Polynomial approximation for the strip weight and complete nodal jet space. -/
theorem twoJetPolynomialApproximation : TwoJetPolynomialApproximation := by
  obtain ⟨J,hJ,happ⟩:=completeJetStripApproximation
  refine ⟨J,0,hJ,?_⟩
  intro N _ hN a
  obtain ⟨b,c,hbc⟩:=twoJetCombination_split N a
  obtain ⟨P,hP,herr⟩:=happ N hN b c
  refine ⟨P,hP,?_⟩
  unfold stripSquaredNorm
  simp_rw [hbc]
  exact herr
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
