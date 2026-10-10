import Mathlib

namespace OAI

/-! Cauchy interpolation residual formulas and their quantitative integral lower bounds. -/

section


namespace Honeycomb370
open Polynomial Finset

noncomputable def cauchyDen {n : ℕ} (u : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (1-C (u i)*X)
noncomputable def cauchyDenExcept {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  ∏ j∈univ.erase i, (1-C (u j)*X)
noncomputable def cauchyNumerator {n : ℕ} (u c : Fin n → ℝ) : Polynomial ℝ :=
  cauchyDen u - ∑ i,C (c i)*(1-X)*cauchyDenExcept u i

lemma cauchyDen_eval {n : ℕ} (u : Fin n → ℝ) (v : ℝ) :
    (cauchyDen u).eval v=∏ i,(1-u i*v) := by simp [cauchyDen,eval_prod]
lemma cauchyDenExcept_eval {n : ℕ} (u : Fin n → ℝ) (i : Fin n) (v : ℝ) :
    (cauchyDenExcept u i).eval v=∏ j∈univ.erase i,(1-u j*v) := by simp [cauchyDenExcept,eval_prod]
lemma cauchyNumerator_one {n : ℕ} (u c : Fin n → ℝ) :
    (cauchyNumerator u c).eval 1=∏ i,(1-u i) := by simp [cauchyNumerator,cauchyDen,eval_prod,eval_finsetSum]
lemma cauchyDen_split {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    cauchyDen u=(1-C (u i)*X)*cauchyDenExcept u i := by
  exact (mul_prod_erase _ _ (mem_univ i)).symm
lemma cauchyNumerator_degree {n : ℕ} (u c : Fin n → ℝ) :
    (cauchyNumerator u c).natDegree≤n := by
  have hlinear (v : ℝ) : (1-C v*X).natDegree≤1 := by
    exact (natDegree_sub_le _ _).trans
      (max_le (by simp) (natDegree_mul_le.trans (by simp)))
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_prod_le _ _).trans (by
      calc
        _≤∑ i : Fin n,1 := sum_le_sum (fun i _ ↦ hlinear (u i))
        _=n := by simp)
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hd : (cauchyDenExcept u i).natDegree≤n-1 := by
      unfold cauchyDenExcept
      calc
        _≤∑ j∈univ.erase i,(1-C (u j)*X : Polynomial ℝ).natDegree := natDegree_prod_le _ _
        (∑ j∈univ.erase i,(1-C (u j)*X : Polynomial ℝ).natDegree)≤∑ j∈univ.erase i,1 :=
          sum_le_sum (fun j _ ↦ hlinear (u j))
        _=n-1 := by simp
    have he : (C (c i)*(1-X)).natDegree≤1 :=
      natDegree_mul_le.trans (by simpa using (hlinear (1:ℝ)))
    exact natDegree_mul_le.trans ((add_le_add he hd).trans (by have := i.isLt; omega))


theorem cauchy_residual_numerator {n : ℕ} (u t c : Fin n → ℝ)
    (ht : Function.Injective t) (ht1 : ∀ j,t j≠1)
    (horth : ∀ j,(cauchyNumerator u c).eval (t j)=0) :
    cauchyNumerator u c =
      C ((∏ i,(1-u i))/(∏ j,(1-t j)))*∏ j,(X-C (t j)) := by
  have hn : ∏ j,(1-t j)≠0 := prod_ne_zero_iff.mpr (fun j _ ↦ sub_ne_zero.mpr (ht1 j).symm)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (f:=Fin.cons 1 t)
  · exact Fin.cons_injective_iff.mpr ⟨by rintro ⟨j,hj⟩; exact ht1 j hj,ht⟩
  · intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [cauchyNumerator_one,eval_prod,hn]
    · rw [Fin.cons_succ,horth j]
      have hz : (∏ k : Fin n,(t j-t k))=0 :=
        prod_eq_zero (mem_univ j) (sub_self _)
      simp [eval_prod,hz]
  · have hp := cauchyNumerator_degree u c
    have hq : (C ((∏ i,(1-u i))/(∏ j,(1-t j)))*∏ j,(X-C (t j))).natDegree≤n := by
      apply natDegree_mul_le.trans
      simp only [natDegree_C,zero_add]
      exact (natDegree_prod_le _ _).trans (by simp)
    simpa using (max_le hp hq).trans_lt (Nat.lt_succ_self n)

end Honeycomb370

end


section

namespace Honeycomb370
open MeasureTheory Set Real Finset

/-- Negative of the exact Cauchy-model transform residual at v=-s.
The 2N common nodes are not symmetrized with the final distinct F/G nodes. -/
noncomputable def sechErrorPositive (N : ℕ) (q : Fin (2*N) → ℝ) (u t s : ℝ) : ℝ :=
  (∏ i,(s+q i)/(1+q i*s)) * ((1-u)*(s+t)/((1-t)*(1+s)*(1+u*s)))

lemma sechErrorPositive_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t s : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1/2) (hu : 0 ≤ u ∧ u ≤ 1/2) (ht : 0 ≤ t ∧ t ≤ 1/2)
    (hs : 0 ≤ s ∧ s ≤ 1) : s^(2*N+1)/8 ≤ sechErrorPositive N q u t s := by
  have hs0 := hs.1
  have hp i : 0<1+q i*s := by nlinarith [mul_nonneg (hq i).1 hs.1]
  have hprod : s^(2*N) ≤ ∏ i : Fin (2*N),(s+q i)/(1+q i*s) := by
    rw [show s^(2*N) = ∏ i : Fin (2*N),s by simp]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ hs.1)
    intro i _
    apply (le_div_iff₀ (hp i)).mpr
    have hss : s^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hss (hq i).1]
  have htpos : 0<1-t := by linarith
  have hup : 0<1+u*s := by nlinarith [mul_nonneg hu.1 hs.1]
  have hden : 0<(1-t)*(1+s)*(1+u*s) := by positivity
  have hden4 : (1-t)*(1+s)*(1+u*s) ≤ 4 := by
    have ha : (1-t)*(1+s) ≤ 2 := calc
      _ ≤ 1*(1+s) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 2 := by linarith
    have hb : 1+u*s ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_left hs.2 hu.1]
    nlinarith
  have hl : s/8 ≤ (1-u)*(s+t)/((1-t)*(1+s)*(1+u*s)) := by
    apply (le_div_iff₀ hden).mpr
    have hn : s/2 ≤ (1-u)*(s+t) := by
      have hh:=mul_le_mul (show (1:ℝ)/2 ≤ 1-u by linarith) (show s ≤ s+t by linarith)
        hs.1 (show 0 ≤ 1-u by linarith)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hden4 hs.1]
  have hm:=mul_le_mul hprod hl (by positivity : 0 ≤ s/8)
    (Finset.prod_nonneg (fun i _ ↦ div_nonneg (by linarith [(hq i).1]) (hp i).le))
  simpa [sechErrorPositive,pow_succ,mul_div_assoc] using hm

lemma cauchy_scale_power_lower (N : ℕ) {p : ℝ} (hp : 2*Real.sqrt ((N:ℝ)+1) ≤ p) :
    (1:ℝ)/2 ≤ (p^2/(1+p^2))^(2*N+1) := by
  have hN : 0<(N:ℝ)+1 := by positivity
  have hs:=Real.sq_sqrt hN.le
  have hp0 : 0 ≤ p := (by positivity : (0:ℝ) ≤ 2*Real.sqrt ((N:ℝ)+1)).trans hp
  have hps : 4*((N:ℝ)+1) ≤ p^2 := by
    nlinarith [sq_le_sq₀ (by positivity : (0:ℝ) ≤ 2*Real.sqrt ((N:ℝ)+1)) hp0 |>.mpr hp]
  have hd : 0<1+p^2 := by positivity
  have hi : (1/(1+p^2):ℝ) ≤ 1 := (div_le_one hd).mpr (by nlinarith [sq_nonneg p])
  have hb := one_add_mul_le_pow (a := -(1/(1+p^2):ℝ)) (by linarith) (2*N+1)
  have he : 1+ -(1/(1+p^2):ℝ)=p^2/(1+p^2) := by field_simp; ring
  rw [he] at hb
  have hc : ((2*N+1:ℕ):ℝ)/(1+p^2) ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    nlinarith
  push_cast at hb hc
  rw [div_eq_mul_inv] at hc
  simp only [one_div,mul_neg] at hb
  linarith

lemma sechErrorPositive_tail_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1/2) (hu : 0 ≤ u ∧ u ≤ 1/2) (ht : 0 ≤ t ∧ t ≤ 1/2)
    {p : ℝ} (hp : 2*Real.sqrt ((N:ℝ)+1) ≤ p) :
    (1:ℝ)/16 ≤ sechErrorPositive N q u t (p^2/(1+p^2)) := by
  have hd : 0<1+p^2 := by positivity
  have hn:=sechErrorPositive_lower N q u t (p^2/(1+p^2)) hq hu ht
    ⟨by positivity,(div_le_one hd).mpr (by linarith)⟩
  have he:=cauchy_scale_power_lower N hp
  linarith

end Honeycomb370

end


section

namespace Honeycomb370
open MeasureTheory Set Real

noncomputable def cauchyEvalFunctional (f : ℝ → ℝ) : ℝ :=
  (2/Real.pi)*(∫ p in Set.Ioi (0:ℝ),f (-p^2/(1+p^2))/(1+p^2))

lemma cauchy_boundary_identity (u p : ℝ) (hu : 0 ≤ u) :
    (1/(1-u*(-p^2/(1+p^2))))/(1+p^2)=1/(1+(1+u)*p^2) := by
  have h₁ : 0<1+p^2 := by positivity
  have h₂ : 0<1+(1+u)*p^2 := by positivity
  have hh : 1-u*(-p^2/(1+p^2))=(1+(1+u)*p^2)/(1+p^2) := by
    field_simp
    ring
  rw [hh]
  field_simp


lemma cauchy_quadratic_integrable (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun p : ℝ ↦ 1/(1+(1+u)*p^2)) := by
  apply integrable_inv_one_add_sq.mono'
  · exact (continuous_const.div (continuous_const.add
      (continuous_const.mul (continuous_id.pow 2)))
      (fun p ↦ ne_of_gt (by positivity : (0:ℝ)<1+(1+u)*p^2))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rw [←one_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_nonneg hu (sq_nonneg p)])

lemma cauchyEval_on_kernel (u : ℝ) (hu : 0 ≤ u) :
    cauchyEvalFunctional (fun v ↦ 1/(1-u*v))=1/Real.sqrt (1+u) := by
  have hs : 0<Real.sqrt (1+u) := Real.sqrt_pos.mpr (by linarith)
  have hss:=Real.sq_sqrt (show 0 ≤ 1+u by linarith)
  unfold cauchyEvalFunctional
  simp_rw [cauchy_boundary_identity u _ hu]
  have he : (fun p : ℝ ↦ 1/(1+(1+u)*p^2))=
      fun p : ℝ ↦ (1+(Real.sqrt (1+u)*p)^2)⁻¹ := by
    ext p
    rw [mul_pow,hss,one_div]
  rw [he,integral_comp_mul_left_Ioi (fun x : ℝ ↦ (1+x^2)⁻¹) 0 hs]
  simp only [mul_zero,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero,smul_eq_mul]
  field_simp

end Honeycomb370

end


section

namespace Honeycomb370
open MeasureTheory Set Real Finset

lemma sechErrorPositive_bounds (N : ℕ) (q : Fin (2*N) → ℝ) (u t s : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1/2) (hu : 0 ≤ u ∧ u ≤ 1/2) (ht : 0 ≤ t ∧ t ≤ 1/2)
    (hs : 0 ≤ s ∧ s ≤ 1) : 0 ≤ sechErrorPositive N q u t s ∧ sechErrorPositive N q u t s ≤ 3 := by
  have hs0:=hs.1
  have hu0:=hu.1
  have hprod : 0 ≤ ∏ i : Fin (2*N),(s+q i)/(1+q i*s) := by
    exact prod_nonneg (fun i _ ↦ div_nonneg (add_nonneg hs.1 (hq i).1)
      (by have := (hq i).1; positivity))
  have hprod1 : (∏ i : Fin (2*N),(s+q i)/(1+q i*s)) ≤ 1 := by
    apply prod_le_one₀ (fun i _ ↦ div_nonneg (add_nonneg hs.1 (hq i).1)
      (by have := (hq i).1; positivity))
    intro i _
    have hd : 0<1+q i*s := by have := (hq i).1; positivity
    apply (div_le_one hd).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ 1-q i by linarith [(hq i).2])]
  have htpos : 0<1-t := by linarith
  have hup : 0<1+u*s := by positivity
  have hden : 0<(1-t)*(1+s)*(1+u*s) := by positivity
  have hdenlo : (1:ℝ)/2 ≤ (1-t)*(1+s)*(1+u*s) := by
    have hmul : 1 ≤ (1+s)*(1+u*s) := by nlinarith [mul_nonneg hu.1 hs.1]
    have hh:=mul_le_mul_of_nonneg_left hmul htpos.le
    nlinarith
  have hnum0 : 0 ≤ (1-u)*(s+t) := mul_nonneg (by linarith) (by linarith [ht.1])
  have hnum : (1-u)*(s+t) ≤ 3/2 := by
    calc
      _ ≤ 1*(s+t) := mul_le_mul_of_nonneg_right (by linarith) (by linarith [ht.1])
      _ ≤ 3/2 := by linarith [ht.2]
  have hlast : 0 ≤ (1-u)*(s+t)/((1-t)*(1+s)*(1+u*s)) := div_nonneg hnum0 hden.le
  have hlast3 : (1-u)*(s+t)/((1-t)*(1+s)*(1+u*s)) ≤ 3 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  refine ⟨mul_nonneg hprod hlast,?_⟩
  exact (mul_le_mul hprod1 hlast3 hlast zero_le_one).trans_eq (one_mul _)

noncomputable def sechErrorIntegrand (N : ℕ) (q : Fin (2*N) → ℝ) (u t p : ℝ) : ℝ :=
  sechErrorPositive N q u t (p^2/(1+p^2))/(1+p^2)

lemma sechErrorIntegrand_integrable (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1/2) (hu : 0 ≤ u ∧ u ≤ 1/2) (ht : 0 ≤ t ∧ t ≤ 1/2) :
    Integrable (sechErrorIntegrand N q u t) := by
  have hs (p : ℝ) : 0 ≤ p^2/(1+p^2) ∧ p^2/(1+p^2) ≤ 1 :=
    ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩
  have hcS : Continuous (fun p : ℝ ↦ p^2/(1+p^2)) := by
    exact (continuous_id.pow 2).div (continuous_const.add (continuous_id.pow 2))
      (fun p ↦ ne_of_gt (by positivity))
  have hd i (p : ℝ) : 1+q i*(p^2/(1+p^2))≠0 := ne_of_gt (by
    have hq0:=(hq i).1
    have hs0:=(hs p).1
    positivity)
  have hd' (p : ℝ) : (1-t)*(1+p^2/(1+p^2))*(1+u*(p^2/(1+p^2)))≠0 := by
    have ht0 : 0<1-t := by linarith [ht.2]
    have hu0:=hu.1
    have hs0:=(hs p).1
    positivity
  have hc : Continuous (sechErrorIntegrand N q u t) := by
    unfold sechErrorIntegrand sechErrorPositive
    apply Continuous.div _ (by fun_prop) (fun p ↦ by positivity)
    apply Continuous.mul
    · apply continuous_finsetProd
      intro i _
      exact (hcS.add continuous_const).div (continuous_const.add (continuous_const.mul hcS)) (hd i)
    · apply Continuous.div (by fun_prop) (by fun_prop) hd'
  apply (integrable_inv_one_add_sq.const_mul 3).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  have hb:=sechErrorPositive_bounds N q u t _ hq hu ht (hs p)
  unfold sechErrorIntegrand
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hb.1 (by positivity))]
  change sechErrorPositive N q u t (p^2/(1+p^2))/(1+p^2) ≤ 3*(1+p^2)⁻¹
  rw [←div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hb.2 (by positivity)


theorem sechModel_integral_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1/2) (hu : 0 ≤ u ∧ u ≤ 1/2) (ht : 0 ≤ t ∧ t ≤ 1/2) :
    1/(136*Real.sqrt ((N:ℝ)+1)) ≤ ∫ p in Set.Ioi (0:ℝ),sechErrorIntegrand N q u t p := by
  let a:=2*Real.sqrt ((N:ℝ)+1)
  let b:=4*Real.sqrt ((N:ℝ)+1)
  have hsq:=Real.sq_sqrt (show 0 ≤ (N:ℝ)+1 by positivity)
  have hroot : 0<Real.sqrt ((N:ℝ)+1) := by positivity
  have hab : a ≤ b := by dsimp [a,b]; nlinarith
  have ha : 0<a := by dsimp [a]; positivity
  have hi:=(sechErrorIntegrand_integrable N q u t hq hu ht).integrableOn (s:=Set.Ioi (0:ℝ))
  have hsub : Set.Icc a b⊆Set.Ioi (0:ℝ) := fun p hp ↦ ha.trans_le hp.1
  have hnon (p : ℝ) : 0 ≤ sechErrorIntegrand N q u t p := by
    apply div_nonneg _ (by positivity)
    exact (sechErrorPositive_bounds N q u t _ hq hu ht
      ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩).1
  have hpoint (p : ℝ) (hp : p∈Set.Icc a b) :
      1/(272*((N:ℝ)+1)) ≤ sechErrorIntegrand N q u t p := by
    have hl:=sechErrorPositive_tail_lower N q u t hq hu ht hp.1
    have hp0 : 0 ≤ p := (ha.trans_le hp.1).le
    have hpu : p^2 ≤ 16*((N:ℝ)+1) := by
      have hh:=sq_le_sq₀ hp0 (show 0 ≤ b by dsimp [b]; positivity) |>.mpr hp.2
      dsimp [b] at hh
      nlinarith
    have hd : 0<1+p^2 := by positivity
    have hN : 0<(N:ℝ)+1 := by positivity
    dsimp [sechErrorIntegrand]
    apply (le_div_iff₀ hd).mpr
    have hr : (1+p^2)/(272*((N:ℝ)+1)) ≤ 1/16 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α:=ℝ) N]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hr.trans hl
  have hmono : (∫ p in Set.Icc a b,(1/(272*((N:ℝ)+1)):ℝ)) ≤
      ∫ p in Set.Icc a b,sechErrorIntegrand N q u t p := by
    apply integral_mono_ae (integrable_const _) (hi.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    exact hpoint p hp
  have hinc : (∫ p in Set.Icc a b,sechErrorIntegrand N q u t p) ≤
      ∫ p in Set.Ioi (0:ℝ),sechErrorIntegrand N q u t p :=
    setIntegral_mono_set hi (Filter.Eventually.of_forall hnon) (Filter.Eventually.of_forall hsub)
  have he : (∫ p in Set.Icc a b,(1/(272*((N:ℝ)+1)):ℝ))=1/(136*Real.sqrt ((N:ℝ)+1)) := by
    rw [setIntegral_const,Real.volume_real_Icc_of_le hab]
    dsimp [a,b]
    field_simp
    nlinarith [hsq]
  rw [he] at hmono
  exact hmono.trans hinc

end Honeycomb370

end


section

namespace Honeycomb370
open Polynomial Finset MeasureTheory Set

noncomputable def cauchyResidual {n : ℕ} (u c : Fin n → ℝ) (v : ℝ) : ℝ :=
  1/(1-v)-∑ i,c i/(1-u i*v)

lemma cauchyResidual_fraction {n : ℕ} (u c : Fin n → ℝ) (v : ℝ)
    (hv : v≠1) (hu : ∀ i,1-u i*v≠0) :
    cauchyResidual u c v=(cauchyNumerator u c).eval v/((1-v)*(cauchyDen u).eval v) := by
  have hd : (cauchyDen u).eval v≠0 := by rw [cauchyDen_eval]; exact prod_ne_zero_iff.mpr (fun i _ ↦ hu i)
  have he (i : Fin n) : (cauchyDen u).eval v=(1-u i*v)*(cauchyDenExcept u i).eval v := by
    rw [cauchyDen_split u i,eval_mul,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  have ht (i : Fin n) : c i/(1-u i*v)*((1-v)*(cauchyDen u).eval v)=
      c i*(1-v)*(cauchyDenExcept u i).eval v := by
    rw [he i]
    field_simp [hu i]
  apply (eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hv.symm) hd)).mpr
  unfold cauchyResidual cauchyNumerator
  rw [eval_sub,eval_finsetSum,sub_mul,Finset.sum_mul]
  simp only [eval_mul,eval_C,eval_sub,eval_one,eval_X]
  simp_rw [ht]
  rw [←mul_assoc,one_div_mul_cancel (sub_ne_zero.mpr hv.symm),one_mul]

lemma cauchyNumerator_zero_of_orth {n : ℕ} (u c : Fin n → ℝ) (v : ℝ)
    (hv : v≠1) (hu : ∀ i,1-u i*v≠0) (ho : 1/(1-v)=∑ i,c i/(1-u i*v)) :
    (cauchyNumerator u c).eval v=0 := by
  have h:=cauchyResidual_fraction u c v hv hu
  have hz : cauchyResidual u c v=0 := sub_eq_zero.mpr ho
  rw [hz] at h
  exact (div_eq_zero_iff.mp h.symm).resolve_right (by
    rw [cauchyDen_eval]
    exact mul_ne_zero (sub_ne_zero.mpr hv.symm) (prod_ne_zero_iff.mpr (fun i _ ↦ hu i)))

lemma cauchyResidual_product {n : ℕ} (u t c : Fin n → ℝ)
    (ht : Function.Injective t) (ht1 : ∀ j,t j≠1)
    (horth : ∀ j,1/(1-t j)=∑ i,c i/(1-u i*t j))
    (hut : ∀ i j,1-u i*t j≠0) (v : ℝ) (hv : v≠1) (huv : ∀ i,1-u i*v≠0) :
    cauchyResidual u c v=((∏ i,(1-u i))/(∏ j,(1-t j)))*(∏ j,(v-t j))/
      ((1-v)*(∏ i,(1-u i*v))) := by
  rw [cauchyResidual_fraction u c v hv huv,cauchyDen_eval,
    cauchy_residual_numerator u t c ht ht1 (fun j ↦ cauchyNumerator_zero_of_orth u c (t j) (ht1 j) (fun i ↦ hut i j) (horth j))]
  simp [eval_prod]

lemma cauchyResidual_common_negative (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (c : Fin (2*N+1) → ℝ) (hq : ∀ i,0≤q i ∧ q i≤1/2) (hu : 0≤u ∧ u≤1/2)
    (ht : 0≤t ∧ t≤1/2) (hinj : Function.Injective (Fin.lastCases t q))
    (horth : ∀ j,1/(1-Fin.lastCases t q j)=
      ∑ i,c i/(1-Fin.lastCases u q i*Fin.lastCases t q j))
    (s : ℝ) (hs : 0 ≤ s) :
    cauchyResidual (Fin.lastCases u q) c (-s) = -sechErrorPositive N q u t s := by
  have hbU (i : Fin (2*N+1)) : (0:ℝ)≤Fin.lastCases u q i ∧ (Fin.lastCases u q i:ℝ)≤1/2 := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hu
    · simpa using hq j
  have hbT (i : Fin (2*N+1)) : (0:ℝ)≤Fin.lastCases t q i ∧ (Fin.lastCases t q i:ℝ)≤1/2 := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using ht
    · simpa using hq j
  have hd (i j : Fin (2*N+1)) : (1:ℝ)-Fin.lastCases u q i*Fin.lastCases t q j≠0 := by
    have hh:=mul_le_mul (hbU i).2 (hbT j).2 (hbT j).1 (by norm_num : (0:ℝ)≤1/2)
    nlinarith
  rw [cauchyResidual_product _ _ _ hinj (fun j ↦ by linarith [(hbT j).2]) horth hd (-s)
    (by linarith) (fun i ↦ by have hh:=mul_nonneg (hbU i).1 hs; nlinarith)]
  simp only [Fin.prod_univ_castSucc,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hprod : (∏ i : Fin (2*N),(-s-q i))=∏ i : Fin (2*N),(s+q i) := by
    simp_rw [show ∀ i : Fin (2*N),-s-q i= -(s+q i) by intro i; ring]
    rw [prod_neg]
    simp [Even.neg_pow (even_two_mul N)]
  have hq0 : ∏ i : Fin (2*N),(1-q i)≠0 := prod_ne_zero_iff.mpr (fun i _ ↦ by linarith [(hq i).2])
  have hqS : ∏ i : Fin (2*N),(1+q i*s)≠0 := prod_ne_zero_iff.mpr (fun i _ ↦ ne_of_gt (by
    have hqi:=(hq i).1; positivity))
  have ht0 : 1-t≠0 := by linarith [ht.2]
  have huS : 1+u*s≠0 := ne_of_gt (by have hu0:=hu.1; positivity)
  have hs1 : 1+s≠0 := ne_of_gt (by positivity)
  rw [hprod]
  simp only [mul_neg,sub_neg_eq_add]
  unfold sechErrorPositive
  rw [prod_div_distrib]
  field_simp
  ring

end Honeycomb370

end


section

namespace Honeycomb370
open MeasureTheory Set Real Finset

lemma cauchyResidual_eval {n : ℕ} (u c : Fin n → ℝ) (hu : ∀ i,0 ≤ u i) :
    cauchyEvalFunctional (cauchyResidual u c)=
      1/Real.sqrt 2-∑ i,c i/Real.sqrt (1+u i) := by
  have hi (v : ℝ) (hv : 0 ≤ v) : IntegrableOn
      (fun p : ℝ ↦ (1/(1-v*(-p^2/(1+p^2))))/(1+p^2)) (Set.Ioi 0) := by
    simp_rw [cauchy_boundary_identity v _ hv]
    exact (cauchy_quadratic_integrable v hv).integrableOn
  have he (p : ℝ) : cauchyResidual u c (-p^2/(1+p^2))/(1+p^2)=
      (1/(1-(1:ℝ)*(-p^2/(1+p^2))))/(1+p^2)-
        ∑ i,c i*((1/(1-u i*(-p^2/(1+p^2))))/(1+p^2)) := by
    unfold cauchyResidual
    rw [sub_div,Finset.sum_div]
    simp only [one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold cauchyEvalFunctional
  simp_rw [he]
  rw [integral_sub (hi 1 zero_le_one) (integrable_finsetSum _ (fun i _ ↦ (hi (u i) (hu i)).const_mul (c i))),
    integral_finsetSum _ (fun i _ ↦ (hi (u i) (hu i)).const_mul (c i)),mul_sub,Finset.mul_sum]
  simp_rw [integral_const_mul]
  have ht:=cauchyEval_on_kernel 1 zero_le_one
  have hf (i : Fin n):=cauchyEval_on_kernel (u i) (hu i)
  change (2/Real.pi)*_-(∑ i,(2/Real.pi)*(c i*_))=_
  simp only [mul_left_comm (2/Real.pi) (c _)]
  change cauchyEvalFunctional (fun v ↦ 1/(1-(1:ℝ)*v))-
    (∑ i,c i*cauchyEvalFunctional (fun v ↦ 1/(1-u i*v)))=_
  rw [ht]
  simp_rw [hf]
  norm_num
  ring_nf

/-- Quantitative evaluation at zero of the exact nonsymmetric Cauchy residual. -/
theorem cauchyResidual_zero_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (c : Fin (2*N+1) → ℝ) (hq : ∀ i,0≤q i ∧ q i≤1/2) (hu : 0≤u ∧ u≤1/2)
    (ht : 0≤t ∧ t≤1/2) (hinj : Function.Injective (Fin.lastCases t q))
    (horth : ∀ j,1/(1-Fin.lastCases t q j)=
      ∑ i,c i/(1-Fin.lastCases u q i*Fin.lastCases t q j)) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤
      -(1/Real.sqrt 2-∑ i,c i/Real.sqrt (1+Fin.lastCases u q i)) := by
  have hb (i : Fin (2*N+1)) : (0:ℝ)≤Fin.lastCases u q i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [hu.1,(hq _).1]
  rw [←cauchyResidual_eval _ c hb]
  have he (p : ℝ) : cauchyResidual (Fin.lastCases u q) c (-p^2/(1+p^2))/(1+p^2)=
      -sechErrorIntegrand N q u t p := by
    rw [neg_div,cauchyResidual_common_negative N q u t c hq hu ht hinj horth _ (by positivity)]
    simp only [sechErrorIntegrand,neg_div]
  unfold cauchyEvalFunctional
  simp_rw [he]
  rw [integral_neg,mul_neg,neg_neg]
  have hh:=mul_le_mul_of_nonneg_left (sechModel_integral_lower N q u t hq hu ht)
    (show 0 ≤ 2/Real.pi by positivity)
  have hec : (2/Real.pi)*(1/(136*Real.sqrt ((N:ℝ)+1)))=
      1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) := by ring
  rwa [hec] at hh

end Honeycomb370

end



end OAI
