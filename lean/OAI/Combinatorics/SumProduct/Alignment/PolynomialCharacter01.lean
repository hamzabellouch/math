import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevHorizontal02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace PolynomialCharacterDescent

lemma derivative_bound (d N : ℕ) (hN : 0 < N) (C : ℝ) (hC : 0 ≤ C)
    (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hc : ∀ j : ℕ, 0 < j → j ≤ d → |p.coeff j| ≤ C/(N:ℝ)^j)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (N:ℝ)) :
    |p.derivative.eval x| ≤ ((d+1):ℝ)*d*C/N := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hterm (j : ℕ) (hj : j ∈ range (d+1)) :
      |p.coeff j*(j:ℝ)*x^(j-1)| ≤ (d:ℝ)*C/N := by
    have hd : j ≤ d := Nat.le_of_lt_succ (mem_range.mp hj)
    by_cases hz : j=0
    · subst j; simp only [Nat.cast_zero,mul_zero,zero_mul,abs_zero]; positivity
    have hjpos : 0 < j := Nat.pos_of_ne_zero hz
    have hpow : (N:ℝ)^j = (N:ℝ)^(j-1)*N := by
      rw [← pow_succ]; congr 1; omega
    have hh := (le_div_iff₀ (pow_pos hNr j)).mp (hc j hjpos hd)
    have hjr : (j:ℝ) ≤ d := by exact_mod_cast hd
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j),abs_of_nonneg (pow_nonneg hx.1 _)]
    apply (le_div_iff₀ hNr).mpr
    have hxpow := pow_le_pow_left₀ hx.1 hx.2 (j-1)
    have hh' : |p.coeff j| *x^(j-1)*N ≤ C := by
      calc
        _ ≤ |p.coeff j| *(N:ℝ)^(j-1)*N := by gcongr
        _ = |p.coeff j| *(N:ℝ)^j := by rw [hpow]; ring
        _ ≤ C := hh
    nlinarith [mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg j),
      mul_le_mul_of_nonneg_right hjr hC]
  rw [derivative_eval, sum_over_range' _ _ (d+1) (Nat.lt_succ_of_le hp)]
  · calc
      _ ≤ ∑ j ∈ range (d+1), |p.coeff j*(j:ℝ)*x^(j-1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range (d+1), (d:ℝ)*C/N := sum_le_sum hterm
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; push_cast; ring
  · intro i; simp

 

lemma linear_residual (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (Q : ℝ[X]) (hQ : Q.natDegree ≤ d) (q : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (m : ℕ → ℤ)
    (hm : ∀ j : ℕ, 2 < j → j ≤ d → |(q:ℝ)*Q.coeff j-m j| ≤ C/(N:ℝ)^j) :
    ∀ h : ℕ, h < N → ∃ z : ℤ,
      |(q:ℝ)*((taylor (h:ℝ) Q-Q).coeff 1)-2*(q:ℝ)*Q.coeff 2*h-z|
        ≤ ((d+1):ℝ)*d*C/N := by
  let u := PolynomialIntegralResidual.integerPart d (fun j => if 2<j then m j else 0)
  let low : ℝ[X] := Polynomial.C (q:ℝ)*Polynomial.C (Q.coeff 0) + Polynomial.C ((q:ℝ)*Q.coeff 1)*X +
    Polynomial.C ((q:ℝ)*Q.coeff 2)*X^2
  let p : ℝ[X] := Polynomial.C (q:ℝ)*Q-low-u.map (Int.castRingHom ℝ)
  have hu (j : ℕ) (hj : j ≤ d) : u.coeff j = if 2<j then m j else 0 :=
    PolynomialIntegralResidual.integerPart_coeff _ _ _ hj
  have hl (j : ℕ) : low.coeff j =
      (if j=0 then (q:ℝ)*Q.coeff 0 else 0)+
      (if j=1 then (q:ℝ)*Q.coeff 1 else 0)+
      (if j=2 then (q:ℝ)*Q.coeff 2 else 0) := by
    simp only [low,coeff_add,coeff_C_mul,coeff_C,coeff_X,coeff_X_pow,mul_ite,mul_one,mul_zero]
    simp only [eq_comm]
  have hpd : p.natDegree ≤ d := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans hQ
      · apply natDegree_add_le_of_degree_le
        · apply natDegree_add_le_of_degree_le
          · exact (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_C] using (Nat.zero_le d))
          · exact (natDegree_C_mul_le _ _).trans (by simpa using (show 1 ≤ d by omega))
        · exact (natDegree_C_mul_le _ _).trans (by simpa using hd)
    · exact natDegree_map_le.trans (PolynomialIntegralResidual.integerPart_degree _ _)
  have hpc (j : ℕ) (hj : 0 < j) (hjd : j ≤ d) : |p.coeff j| ≤ C/(N:ℝ)^j := by
    dsimp [p]
    rw [coeff_sub,coeff_sub,coeff_C_mul,coeff_map,hu j hjd,hl]
    by_cases hj2 : 2<j
    · simpa [ne_of_gt hj,show j≠1 by omega,show j≠2 by omega,hj2] using hm j hj2 hjd
    · have he : j=1 ∨ j=2 := by omega
      rcases he with rfl | rfl <;> norm_num <;> positivity
  intro h hh
  have hbound := derivative_bound d N hN C hC p hpd hpc h
    ⟨Nat.cast_nonneg _,by exact_mod_cast hh.le⟩
  have huval : (u.map (Int.castRingHom ℝ)).derivative.eval (h:ℝ) =
      ((u.derivative.eval (h:ℤ):ℤ):ℝ) := by
    rw [derivative_map,eval_map]
    exact eval₂_at_apply (Int.castRingHom ℝ) (h:ℤ)
  refine ⟨u.derivative.eval h,?_⟩
  convert hbound using 2
  simp only [p,derivative_sub,derivative_C_mul,eval_sub,eval_mul,eval_C,huval,
    coeff_sub,taylor_coeff_one]
  simp only [low,derivative_add,derivative_mul,derivative_C,zero_mul,derivative_X,
    mul_one,derivative_pow,eval_add,eval_mul,eval_C]
  norm_num
  ring

 

theorem polynomial_descent (d : ℕ) (hd : 2 ≤ d) (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P Q : ℝ[X], Q.natDegree ≤ d →
        ∀ σ : ℕ → ℝ, ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
        (∀ h ∈ S, ∃ z : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff 2-z| ≤ A/(N:ℝ)^2) →
        (∀ h ∈ S, ∃ z : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff 1+σ h-z| ≤ A/N) →
        ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ B ∧
          (∀ j : ℕ, 2 < j → j ≤ d → ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m| ≤ C/(N:ℝ)^j) ∧
          (∀ h ∈ S, ∃ z : ℤ, |(q:ℝ)*P.coeff 1+2*(q:ℝ)*Q.coeff 2*h+(q:ℝ)*σ h-z| ≤ C/N) := by
  classical
  obtain ⟨B,hB,C,hC,L,hL,hdesc⟩ := high_coefficients d δ A hδ hA
  let C' := max C ((B:ℝ)*A+((d+1):ℝ)*d*C)
  have hCC : C ≤ C' := le_max_left _ _
  have hsum : (B:ℝ)*A+((d+1):ℝ)*d*C ≤ C' := le_max_right _ _
  refine ⟨B,hB,C',hC.trans_le hCC,L,hL,?_⟩
  intro N hLN P Q hQ σ S hSN hS hsecond hfirst
  have hN : 0<N := hL.trans_le hLN
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  obtain ⟨q,hq,hqB,hcoeff⟩ := hdesc N hLN P Q hQ S hSN hS hsecond
  have hex (j : ℕ) : ∃ m : ℤ, 2<j → j≤d → |(q:ℝ)*Q.coeff j-m| ≤ C/(N:ℝ)^j := by
    by_cases hj : 2<j ∧ j≤d
    · obtain ⟨m,hm⟩ := hcoeff j hj.1 hj.2; exact ⟨m,fun _ _ => hm⟩
    · exact ⟨0,fun h₁ h₂ => False.elim (hj ⟨h₁,h₂⟩)⟩
  choose m hm using hex
  refine ⟨q,hq,hqB,?_,?_⟩
  · intro j hj hjd
    exact ⟨m j,(hm j hj hjd).trans (div_le_div_of_nonneg_right hCC (by positivity))⟩
  · intro h hh
    obtain ⟨z,hz⟩ := linear_residual d N hd hN Q hQ q C hC.le m hm h (mem_range.mp (hSN hh))
    obtain ⟨k,hk⟩ := hfirst h hh
    have hqR : |(q:ℝ)| ≤ B := by exact_mod_cast hqB
    refine ⟨q*k-z,?_⟩
    calc
      _ = |(q:ℝ)*((P+taylor (h:ℝ) Q-Q).coeff 1+σ h-k)-
          ((q:ℝ)*(taylor (h:ℝ) Q-Q).coeff 1-2*(q:ℝ)*Q.coeff 2*h-z)| := by
        push_cast
        congr 1
        simp only [coeff_sub,coeff_add]
        ring
      _ ≤ |(q:ℝ)*((P+taylor (h:ℝ) Q-Q).coeff 1+σ h-k)|+
          |(q:ℝ)*(taylor (h:ℝ) Q-Q).coeff 1-2*(q:ℝ)*Q.coeff 2*h-z| := abs_sub _ _
      _ ≤ (B:ℝ)*(A/N)+((d+1):ℝ)*d*C/N := by
        apply add_le_add _ hz
        rw [abs_mul]
        exact mul_le_mul hqR hk (abs_nonneg _) (Nat.cast_nonneg B)
      _ = ((B:ℝ)*A+((d+1):ℝ)*d*C)/N := by ring
      _ ≤ C'/N := div_le_div_of_nonneg_right hsum hNr.le

end PolynomialCharacterDescent
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace PolynomialCharacterDescent

lemma taylor_coefficient_bound (d N : ℕ) (hN : 0<N) (C : ℝ) (hC : 0≤C)
    (p : ℝ[X]) (hp : p.natDegree≤d)
    (hc : ∀ j : ℕ, 0<j → j≤d → |p.coeff j|≤C/(N:ℝ)^j)
    (j : ℕ) (hj : 0<j) (x : ℝ) (hx : x∈Set.Icc 0 (N:ℝ)) :
    |(taylor x p).coeff j|≤((d+1):ℝ)*(2:ℝ)^d*C/(N:ℝ)^j := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hdeg : (hasseDeriv j p).natDegree≤d :=
    (natDegree_hasseDeriv_le p j).trans ((Nat.sub_le _ _).trans hp)
  rw [taylor_coeff,eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  have hterm (k : ℕ) (hk : k∈range (d+1)) :
      |((hasseDeriv j p).coeff k)*x^k|≤(2:ℝ)^d*C/(N:ℝ)^j := by
    rw [hasseDeriv_coeff]
    by_cases hkj : k+j≤d
    · have hcoef := (le_div_iff₀ (pow_pos hNr (k+j))).mp (hc (k+j) (by omega) hkj)
      have hchoose : ((k+j).choose j:ℝ)≤(2:ℝ)^d := by
        have hh := Nat.choose_le_two_pow (k+j) j
        exact_mod_cast hh.trans (Nat.pow_le_pow_right (by norm_num) hkj)
      have hsmall : |p.coeff (k+j)| * x^k*(N:ℝ)^j≤C := by
        calc
          _ ≤ |p.coeff (k+j)| * (N:ℝ)^k*(N:ℝ)^j := by gcongr <;> first | exact hx.1 | exact hx.2
          _ = |p.coeff (k+j)| * (N:ℝ)^(k+j) := by rw [pow_add]; ring
          _ ≤ C := hcoef
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (pow_nonneg hx.1 _)]
      apply (le_div_iff₀ (pow_pos hNr j)).mpr
      calc
        _ = ((k+j).choose j:ℝ)*(|p.coeff (k+j)| * x^k*(N:ℝ)^j) := by ring
        _ ≤ ((k+j).choose j:ℝ)*C := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right hchoose hC
    · rw [coeff_eq_zero_of_natDegree_lt (by omega),mul_zero,zero_mul,abs_zero]
      positivity
  calc
    _ ≤ ∑ k∈range (d+1),|((hasseDeriv j p).coeff k)*x^k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k∈range (d+1),(2:ℝ)^d*C/(N:ℝ)^j := sum_le_sum hterm
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; push_cast; ring

 

lemma nonlinear_shift_residual (d N : ℕ) (hd : 1≤d) (hN : 0<N)
    (Q : ℝ[X]) (hQ : Q.natDegree≤d) (q : ℤ) (C : ℝ) (hC : 0≤C)
    (m : ℕ → ℤ)
    (hm : ∀ j : ℕ, 1<j → j≤d → |(q:ℝ)*Q.coeff j-m j|≤C/(N:ℝ)^j) :
    ∀ h : ℕ, h<N → ∀ j : ℕ, 0<j → j≤d → ∃ z : ℤ,
      |(q:ℝ)*((taylor (h:ℝ) Q-Q).coeff j)-z|
        ≤ (((d+1):ℝ)*(2:ℝ)^d+1)*C/(N:ℝ)^j := by
  let u := PolynomialIntegralResidual.integerPart d (fun j => if 1<j then m j else 0)
  let low : ℝ[X] := Polynomial.C ((q:ℝ)*Q.coeff 0) + Polynomial.C ((q:ℝ)*Q.coeff 1)*X
  let p : ℝ[X] := Polynomial.C (q:ℝ)*Q-low-u.map (Int.castRingHom ℝ)
  have hu (j : ℕ) (hj : j≤d) : u.coeff j = if 1<j then m j else 0 :=
    PolynomialIntegralResidual.integerPart_coeff _ _ _ hj
  have hl (j : ℕ) : low.coeff j =
      (if j=0 then (q:ℝ)*Q.coeff 0 else 0)+(if j=1 then (q:ℝ)*Q.coeff 1 else 0) := by
    simp only [low,coeff_add,coeff_C_mul,coeff_C,coeff_X,mul_ite,mul_one,mul_zero]
    simp only [eq_comm]
  have hpd : p.natDegree≤d := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans hQ
      · apply natDegree_add_le_of_degree_le
        · exact (natDegree_C _).trans_le (Nat.zero_le d)
        · exact (natDegree_C_mul_le _ _).trans (by simpa using hd)
    · exact natDegree_map_le.trans (PolynomialIntegralResidual.integerPart_degree _ _)
  have hpc (j : ℕ) (hj : 0<j) (hjd : j≤d) : |p.coeff j|≤C/(N:ℝ)^j := by
    dsimp [p]
    rw [coeff_sub,coeff_sub,coeff_C_mul,coeff_map,hu j hjd,hl]
    by_cases hj1 : 1<j
    · simpa [ne_of_gt hj,show j≠1 by omega,hj1] using hm j hj1 hjd
    · have he : j=1 := by omega
      subst j; norm_num; positivity
  intro h hh j hj hjd
  have hbound := taylor_coefficient_bound d N hN C hC p hpd hpc j hj h
    ⟨Nat.cast_nonneg _,by exact_mod_cast hh.le⟩
  have hdiff : |(taylor (h:ℝ) p-p).coeff j|≤(((d+1):ℝ)*(2:ℝ)^d+1)*C/(N:ℝ)^j := by
    rw [coeff_sub]
    calc
      _ ≤ |(taylor (h:ℝ) p).coeff j|+|p.coeff j| := abs_sub _ _
      _ ≤ ((d+1):ℝ)*(2:ℝ)^d*C/(N:ℝ)^j+C/(N:ℝ)^j := add_le_add hbound (hpc j hj hjd)
      _ = _ := by ring
  have he : taylor (h:ℝ) p-p =
      Polynomial.C (q:ℝ)*(taylor (h:ℝ) Q-Q) -
      (taylor (h:ℤ) u-u).map (Int.castRingHom ℝ) - Polynomial.C ((q:ℝ)*Q.coeff 1*h) := by
    simp only [p,low,taylor_apply,sub_comp,add_comp,C_mul_comp,C_comp,X_comp,
      Polynomial.map_sub,map_comp,Polynomial.map_add,map_X,map_C,Int.coe_castRingHom,Int.cast_natCast]
    simp only [map_mul]
    ring
  refine ⟨(taylor (h:ℤ) u-u).coeff j,?_⟩
  simpa only [he,coeff_sub,coeff_C_mul,coeff_map,coeff_C,ite_eq_right (ne_of_gt hj),sub_zero,
    Int.coe_castRingHom] using hdiff

 

theorem zero_commutator_descent (d : ℕ) (hd : 1≤d) (δ A : ℝ) (hδ : 0<δ) (hA : 0≤A) :
    ∃ B : ℕ, 0<B ∧ ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀≤N → ∀ P Q : ℝ[X], P.natDegree≤d → Q.natDegree≤d →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ h∈S, ∀ j : ℕ, 0<j → j≤d → ∃ z : ℤ,
        |(P+taylor (h:ℝ) Q-Q).coeff j-z|≤A/(N:ℝ)^j) →
      ∃ q : ℤ, q≠0 ∧ |q|≤B ∧
        (∀ j : ℕ, 0<j → ∃ m : ℤ, |(q:ℝ)*P.coeff j-m|≤C/(N:ℝ)^j) ∧
        (∀ j : ℕ, 1<j → ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m|≤C/(N:ℝ)^j) := by
  classical
  obtain ⟨B,hB,C,hC,L,hL,hdesc⟩ := shift_coefficients d 1 (by decide) δ A hδ hA
  let D := (((d+1):ℝ)*(2:ℝ)^d+1)*C
  let C' := max C ((B:ℝ)*A+D)
  have hCC : C≤C' := le_max_left _ _
  have hsum : (B:ℝ)*A+D≤C' := le_max_right _ _
  refine ⟨B,hB,C',hC.trans_le hCC,L,hL,?_⟩
  intro N hLN P Q hP hQ S hSN hS hsmall
  have hN : 0<N := hL.trans_le hLN
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  obtain ⟨q,hq,hqB,hcoeff⟩ := hdesc N hLN P Q hQ S hSN hS
    (fun h hh => hsmall h hh 1 (by decide) hd)
  have hex (j : ℕ) : ∃ m : ℤ, 1<j → j≤d → |(q:ℝ)*Q.coeff j-m|≤C/(N:ℝ)^j := by
    by_cases hj : 1<j ∧ j≤d
    · obtain ⟨m,hm⟩ := hcoeff j hj.1 hj.2
      exact ⟨m,fun _ _ => hm⟩
    · exact ⟨0,fun h1 h2 => (hj ⟨h1,h2⟩).elim⟩
  choose m hm using hex
  have hres := nonlinear_shift_residual d N hd hN Q hQ q C hC.le m hm
  have hqBr : |(q:ℝ)|≤B := by exact_mod_cast hqB
  refine ⟨q,hq,hqB,?_,?_⟩
  · intro j hj
    by_cases hjd : j≤d
    · have hpos : (0:ℝ)<S.card := (mul_pos hδ hNr).trans_le hS
      obtain ⟨h,hh⟩ := card_pos.mp (by exact_mod_cast hpos)
      obtain ⟨z,hz⟩ := hsmall h hh j hj hjd
      obtain ⟨w,hw⟩ := hres h (mem_range.mp (hSN hh)) j hj hjd
      refine ⟨q*z-w,?_⟩
      have hz' : |(q:ℝ)*((P+taylor (h:ℝ) Q-Q).coeff j-z)|≤(B:ℝ)*A/(N:ℝ)^j := by
        rw [abs_mul]
        calc
          _ ≤ (B:ℝ)*(A/(N:ℝ)^j) := mul_le_mul hqBr hz (abs_nonneg _) (Nat.cast_nonneg _)
          _ = _ := by ring
      have he : (q:ℝ)*P.coeff j-((q*z-w:ℤ):ℝ) =
          (q:ℝ)*((P+taylor (h:ℝ) Q-Q).coeff j-z)-
          ((q:ℝ)*((taylor (h:ℝ) Q-Q).coeff j)-w) := by
        simp only [coeff_sub,coeff_add,Int.cast_sub,Int.cast_mul]
        ring
      rw [he]
      calc
        _ ≤ |(q:ℝ)*((P+taylor (h:ℝ) Q-Q).coeff j-z)|+
            |(q:ℝ)*((taylor (h:ℝ) Q-Q).coeff j)-w| := abs_sub _ _
        _ ≤ (B:ℝ)*A/(N:ℝ)^j+D/(N:ℝ)^j := add_le_add hz' hw
        _ = ((B:ℝ)*A+D)/(N:ℝ)^j := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hsum (pow_nonneg hNr.le _)
    · refine ⟨0,?_⟩
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [mul_zero,Int.cast_zero,sub_zero,abs_zero]
      exact div_nonneg (hC.le.trans hCC) (pow_nonneg hNr.le _)
  · intro j hj
    by_cases hjd : j≤d
    · exact ⟨m j,(hm j hj hjd).trans (div_le_div_of_nonneg_right hCC (pow_nonneg hNr.le _))⟩
    · refine ⟨0,?_⟩
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [mul_zero,Int.cast_zero,sub_zero,abs_zero]
      exact div_nonneg (hC.le.trans hCC) (pow_nonneg hNr.le _)

end PolynomialCharacterDescent

end
end
end
end
end

end OAI
