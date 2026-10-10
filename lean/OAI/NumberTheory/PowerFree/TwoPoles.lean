import OAI.NumberTheory.PowerFree.ThreePoles

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators Classical

lemma fin_sum_nat_cast (M : ℕ) : ∑ m : Fin (M+1), (m.val:ℝ) = (M:ℝ)*(M+1)/2 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hh := congrArg (fun n : ℕ => (n:ℝ)) (Finset.sum_range_id_mul_two (M+1))
  norm_num only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_sum] at hh
  linarith

theorem pole_family_count_lower (U V T : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hT : U ≤ T) :
    let M := ⌊(T-U)/V⌋₊
    let N := fun m : Fin (M+1) => ⌊(T-V*m.val)/U⌋₊+1
    ((V+4*U)/(2*U*V^2))*T^2-((V+4*U)*(U+V)/(U*V^2))*T ≤
      (∑ m : Fin (M+1), (N m:ℝ))+2*(M:ℝ)*(M+1) := by
  dsimp only
  let M := ⌊(T-U)/V⌋₊
  let N := fun m : Fin (M+1) => ⌊(T-V*m.val)/U⌋₊+1
  change _ ≤ (∑ m : Fin (M+1), (N m:ℝ))+2*(M:ℝ)*(M+1)
  have hT0 : 0 ≤ T := hU.le.trans hT
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hMle : (M:ℝ) ≤ (T-U)/V := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) hV.le)
  have hMgt : (T-U)/V < (M:ℝ)+1 := Nat.lt_floor_add_one _
  have hVM : V*(M:ℝ) ≤ T-U := by simpa only [mul_comm] using (le_div_iff₀ hV).mp hMle
  have hVM' : T-U < V*((M:ℝ)+1) := by simpa only [mul_comm] using (div_lt_iff₀ hV).mp hMgt
  have hN (m : Fin (M+1)) : V/U*((M:ℝ)-m.val) ≤ (N m:ℝ) := by
    have hmf : (m.val:ℝ) ≤ M := by exact_mod_cast (show m.val ≤ M by omega)
    have hfloor : (T-V*m.val)/U < (N m:ℝ) := by
      simpa only [N,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one ((T-V*m.val)/U)
    have hbase : V*((M:ℝ)-m.val) ≤ T-V*m.val := by nlinarith
    have hh := div_le_div_of_nonneg_right hbase hU.le
    calc V/U*((M:ℝ)-m.val) = V*((M:ℝ)-m.val)/U := by ring
      _ ≤ (T-V*m.val)/U := hh
      _ ≤ (N m:ℝ) := hfloor.le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun m (_ : m ∈ Finset.univ) => hN m)
  have he : (∑ m : Fin (M+1), V/U*((M:ℝ)-m.val)) = V/(2*U)*(M:ℝ)*(M+1) := by
    rw [←Finset.mul_sum]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [fin_sum_nat_cast]
    push_cast
    ring
  rw [he] at hsum
  have hsq : T^2 - 2*(U+V)*T ≤ V^2*(M:ℝ)^2 := by
    have hp : 0 ≤ (T-V*(M:ℝ)) := by linarith
    have hq : T-V*(M:ℝ) ≤ U+V := by linarith
    have hc : T+V*(M:ℝ) ≤ 2*T := by linarith
    have hmul := mul_le_mul hq hc (by positivity : 0 ≤ T+V*(M:ℝ)) (by positivity : 0 ≤ U+V)
    nlinarith
  have hc : 0 < (V+4*U)/(2*U*V^2) := by positivity
  have hh := mul_le_mul_of_nonneg_left hsq hc.le
  have heq : ((V+4*U)/(2*U*V^2))*(V^2*(M:ℝ)^2) = (V/(2*U)+2)*(M:ℝ)^2 := by field_simp; ring
  rw [heq] at hh
  have hlin : 0 ≤ (V/(2*U)+2)*(M:ℝ) := by positivity
  have hcoeff : (V+4*U)/(2*U*V^2)*(2*(U+V)*T) = (V+4*U)*(U+V)/(U*V^2)*T := by ring
  rw [mul_sub,hcoeff] at hh
  nlinarith

open scoped BigOperators Classical
open MvPolynomial

lemma weightedFunctions_algebraMap {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {U : ℝ} (hU : 0 ≤ U) (c : K) :
    algebraMap K (MvPolynomial σ K ⧸ I) c ∈ weightedFunctions I ω U := by
  have hh := (weightedFunctions I ω U).smul_mem c
    (weightedFunctions_mono I ω hω hU (weightedFunctions_one I ω hω))
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

lemma threePoleFunction_weighted {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (t b₀ : MvPolynomial σ K ⧸ I) (a b : Fin 2 → MvPolynomial σ K ⧸ I)
    (U V T : ℝ) (ht : t ∈ weightedFunctions I ω U)
    (hb₀ : b₀ ∈ weightedFunctions I ω V) (ha : ∀ i, a i ∈ weightedFunctions I ω U)
    (hb : ∀ i, b i ∈ weightedFunctions I ω V)
    (m N : ℕ) (hN : ∀ j : Fin N, U*j.val+V*m ≤ T)
    (hm : ∀ e : Fin 2, V*m+U*e.val ≤ T)
    (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) :
    threePoleFunction t b₀ a b m N i ∈ weightedFunctions I ω T := by
  cases i with
  | inl j =>
    exact weightedFunctions_mono I ω hω (hN j)
      (weightedFunctions_mul I ω hω (weightedFunctions_pow I ω hω ht j.val)
        (weightedFunctions_pow I ω hω hb₀ m))
  | inr z =>
    rcases z with ⟨s,j,e⟩
    apply weightedFunctions_mono I ω hω _
      (weightedFunctions_mul I ω hω
        (weightedFunctions_mul I ω hω
          (weightedFunctions_pow I ω hω hb₀ (m-(j.val+1)))
          (weightedFunctions_pow I ω hω (hb s) (j.val+1)))
        (weightedFunctions_pow I ω hω (ha s) e.val))
    have hj : j.val+1 ≤ m := by omega
    rw [Nat.cast_sub hj]
    nlinarith [hm e]

theorem threePole_hilbert_lower {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (hr₀ : ∀ i, r i ≠ r₀) (hr : Function.Injective r)
    (t q b₀ : MvPolynomial σ K ⧸ I) (b : Fin 2 → MvPolynomial σ K ⧸ I)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t)))
    (h₀ : (t-algebraMap K _ r₀)^2*b₀=q-algebraMap K _ θ₀)
    (h : ∀ i, (t-algebraMap K _ (r i))^2*b i=q-algebraMap K _ (θ i))
    (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht : t ∈ weightedFunctions I ω U) (hb₀ : b₀ ∈ weightedFunctions I ω V)
    (hb : ∀ i, b i ∈ weightedFunctions I ω V) :
    ∀ T : ℝ, 0 ≤ T → ((V+4*U)/(2*U*V^2))*T^2-
      ((V+4*U)*(U+V)/(U*V^2))*T ≤ weightedHilbert I ω T := by
  intro T hT0
  by_cases hT : U ≤ T
  · let M := ⌊(T-U)/V⌋₊
    let N := fun m : Fin (M+1) => ⌊(T-V*m.val)/U⌋₊+1
    let ι := Σ m : Fin (M+1), (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2)
    let v : ι → MvPolynomial σ K ⧸ I := fun i =>
      threePoleFunction t b₀ (fun i => t-algebraMap K _ (r i)) b i.1.val (N i.1) i.2
    have hM : V*(M:ℝ) ≤ T-U := by
      have hh := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) hV.le)
      simpa only [mul_comm] using (le_div_iff₀ hV).mp hh
    have hv (i : ι) : v i ∈ weightedFunctions I ω T := by
      apply threePoleFunction_weighted I ω hω t b₀ _ b U V T ht hb₀
        (fun j => (weightedFunctions I ω U).sub_mem ht (weightedFunctions_algebraMap I ω hω hU.le (r j))) hb
      · intro j
        have hm : (i.1.val:ℝ) ≤ M := by exact_mod_cast (show i.1.val ≤ M by omega)
        have hn : 0 ≤ T-V*i.1.val := by nlinarith
        have hj : (j.val:ℝ) ≤ ⌊(T-V*i.1.val)/U⌋₊ := by
          exact_mod_cast (show j.val ≤ ⌊(T-V*i.1.val)/U⌋₊ by have := j.isLt; dsimp [N] at this; omega)
        have hf := hj.trans (Nat.floor_le (div_nonneg hn hU.le))
        have hh := (le_div_iff₀ hU).mp hf
        nlinarith
      · intro e
        have hm : (i.1.val:ℝ) ≤ M := by exact_mod_cast (show i.1.val ≤ M by omega)
        have he : (e.val:ℝ) ≤ 1 := by exact_mod_cast (show e.val ≤ 1 by omega)
        nlinarith [mul_le_mul_of_nonneg_left hm hV.le,mul_le_mul_of_nonneg_left he hU.le]
    have hi' : LinearIndependent K v := threePole_functions_independent r₀ θ₀ r θ hr₀ hr t q b₀ b hi h₀ h M N
    let u : ι → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
    have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype hi'
    have hcard : (Fintype.card ι:ℝ) ≤ weightedHilbert I ω T := by
      exact_mod_cast hu.fintype_card_le_finrank
    have hce : (Fintype.card ι:ℝ) = (∑ m : Fin (M+1), (N m:ℝ))+2*(M:ℝ)*(M+1) := by
      simp only [ι,Fintype.card_sigma,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,
        Nat.cast_sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Finset.sum_add_distrib]
      simp_rw [mul_assoc,←Finset.mul_sum]
      rw [show (∑ m : Fin (M+1), (m.val:ℝ)*2) = (∑ m : Fin (M+1), (m.val:ℝ))*2 by rw [Finset.sum_mul]]
      rw [fin_sum_nat_cast]
      ring
    rw [hce] at hcard
    exact (pole_family_count_lower U V T hU hV hT).trans hcard
  · have hc : 0 < (V+4*U)/(2*U*V^2) := by positivity
    have he : (V+4*U)*(U+V)/(U*V^2) = ((V+4*U)/(2*U*V^2))*(2*(U+V)) := by ring
    rw [he]
    have hh : ((V+4*U)/(2*U*V^2))*T^2-
        ((V+4*U)/(2*U*V^2))*(2*(U+V))*T ≤ 0 := by
      have hsmall : T ≤ 2*(U+V) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsmall hT0,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hT0) hc.le]
    exact hh.trans (Nat.cast_nonneg _)
end

open Polynomial
open scoped BigOperators Classical

private lemma coeff_linear_power {K : Type*} [CommRing K] [Nontrivial K] (c : K) (m : ℕ) :
    ((X-C c)^m : Polynomial K).coeff m = 1 := by
  have h1 : (X-C c : Polynomial K).coeff 1 = 1 := by simp
  have h := coeff_pow_of_natDegree_le (m := m) (n := 1) (p := (X-C c : Polynomial K)) (by simp)
  rw [mul_one,h1,one_pow] at h
  exact h

noncomputable def twoPolePolynomial {K : Type*} [Field K]
    (r₀ r₁ θ₀ θ₁ : K) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) : Polynomial (Polynomial K) :=
  let H := (X-C r₁)^(2*(M-m))
  i.elim
    (fun a => C (H*(X^a.val*((X-C r₀)^(2*(M-m))*(X-C r₁)^(2*m))))*(X-C (C θ₀))^m)
    (fun j => C (H*twoPoleNumerator r₀ r₁ m (M-m) j)*
      j.elim (fun e => (X-C (C θ₀))^(m-(e.1.val+1))*(X-C (C θ₁))^(e.1.val+1))
        (fun _ => (X-C (C θ₀))^m))

lemma twoPolePolynomial_degree {K : Type*} [Field K]
    (r₀ r₁ θ₀ θ₁ : K) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) :
    (twoPolePolynomial r₀ r₁ θ₀ θ₁ M m N i).natDegree ≤ m := by
  cases i with
  | inl a =>
    dsimp only [twoPolePolynomial,Sum.elim_inl]
    exact (natDegree_C_mul_le _ _).trans (by simp)
  | inr j =>
    cases j with
    | inl e =>
      apply (natDegree_C_mul_le _ _).trans
      have hj : m-(e.1.val+1)+(e.1.val+1)=m := by have := e.1.isLt; omega
      calc
        _ ≤ (m-(e.1.val+1))+(e.1.val+1) := by
          apply natDegree_mul_le.trans
          simp
        _ = m := hj
    | inr e =>
      dsimp only [twoPolePolynomial,Sum.elim_inr]
      exact (natDegree_C_mul_le _ _).trans (by simp)

lemma twoPolePolynomial_coeff {K : Type*} [Field K]
    (r₀ r₁ θ₀ θ₁ : K) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) :
    (twoPolePolynomial r₀ r₁ θ₀ θ₁ M m N i).coeff m =
      (X-C r₁)^(2*(M-m))*
        Sum.elim (fun a : Fin N => X^a.val*((X-C r₀)^(2*(M-m))*(X-C r₁)^(2*m)))
          (twoPoleNumerator r₀ r₁ m (M-m)) i := by
  cases i with
  | inl a => simp only [twoPolePolynomial,Sum.elim_inl,coeff_C_mul,coeff_linear_power,mul_one]
  | inr j =>
    cases j with
    | inl e =>
      simp only [twoPolePolynomial,Sum.elim_inr,Sum.elim_inl,coeff_C_mul]
      have hj : m-(e.1.val+1)+(e.1.val+1)=m := by have := e.1.isLt; omega
      have hh : (((X-C (C θ₀))^(m-(e.1.val+1)))*(X-C (C θ₁))^(e.1.val+1) : Polynomial (Polynomial K)).coeff m = 1 := by
        calc
          _ = (((X-C (C θ₀))^(m-(e.1.val+1)))*(X-C (C θ₁))^(e.1.val+1) : Polynomial (Polynomial K)).coeff
            ((m-(e.1.val+1))+(e.1.val+1)) := congrArg _ hj.symm
          _ = _ := coeff_mul_add_eq_of_natDegree_le (by simp) (by simp)
          _ = 1 := by rw [coeff_linear_power,coeff_linear_power,one_mul]
      rw [hh,mul_one]
    | inr e => simp only [twoPolePolynomial,Sum.elim_inr,coeff_C_mul,coeff_linear_power,mul_one]

theorem twoPole_polynomials_independent {K : Type*} [Field K]
    (r₀ r₁ θ₀ θ₁ : K) (hr : r₀ ≠ r₁) (M : ℕ) (N : Fin (M+1) → ℕ) :
    LinearIndependent K (fun i : Σ m : Fin (M+1), Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2)) =>
      twoPolePolynomial r₀ r₁ θ₀ θ₁ M i.1.val (N i.1) i.2) := by
  let ι := fun m : Fin (M+1) => Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2))
  let p := fun (m : Fin (M+1)) => twoPolePolynomial r₀ r₁ θ₀ θ₁ M m.val (N m)
  let φ := fun m => (Polynomial.lcoeff (Polynomial K) m).restrictScalars K
  change LinearIndependent K (fun i : Σ m, ι m => p i.1 i.2)
  refine linearIndependent_of_fin_top_blocks M ι p φ ?_ ?_
  · intro m i n hmn
    exact coeff_eq_zero_of_natDegree_lt ((twoPolePolynomial_degree r₀ r₁ θ₀ θ₁ M m.val (N m) i).trans_lt hmn)
  · intro m
    have hb := twoPole_leading_independent r₀ r₁ hr m.val (M-m.val) (N m)
    have hH : (X-C r₁)^(2*(M-m.val)) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
    have hi := hb.map' (LinearMap.mulLeft K ((X-C r₁)^(2*(M-m.val))))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hH))
    have heq : (fun i => φ m.val (p m i)) =
        (LinearMap.mulLeft K ((X-C r₁)^(2*(M-m.val)))) ∘
          Sum.elim (fun a : Fin (N m) => X^a.val*((X-C r₀)^(2*(M-m.val))*(X-C r₁)^(2*m.val)))
            (twoPoleNumerator r₀ r₁ m.val (M-m.val)) := by
      funext i
      exact twoPolePolynomial_coeff r₀ r₁ θ₀ θ₁ M m.val (N m) i
    rw [heq]
    exact hi

noncomputable def twoPoleFunction {L : Type*} [CommRing L]
    (t a₀ a₁ b₀ b₁ u₀ : L) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) : L :=
  i.elim (fun j => t^j.val*b₀^m)
    (Sum.elim (fun j => b₀^(m-(j.1.val+1))*b₁^(j.1.val+1)*a₁^j.2.val)
      (fun j => b₀^m*u₀^(j.1.val+1)*a₀^j.2.val))

lemma twoPole_extra_right_identity {R : Type*} [CommRing R] (a₀ a₁ b₀ u₀ c₀ : R)
    (h₀ : a₀^2*b₀=c₀) (hu : a₀^2*u₀=1) (M m j e : ℕ) (hm : m ≤ M) (hj : j ≤ M-m) :
    (a₀^(2*M)*a₁^(2*M))*(b₀^m*u₀^j*a₀^e) =
      a₁^(2*(M-m))*(a₀^(2*((M-m)-j)+e)*a₁^(2*m))*c₀^m := by
  have h0 := square_relation_power a₀ b₀ c₀ h₀ M m hm
  have h1 := square_relation_power a₀ u₀ 1 hu (M-m) j hj
  rw [one_pow,mul_one] at h1
  have he : 2*M = 2*(M-m)+2*m := by omega
  calc
    _ = (a₀^(2*M)*b₀^m)*u₀^j*a₀^e*a₁^(2*M) := by ring
    _ = (a₀^(2*(M-m))*u₀^j)*c₀^m*a₀^e*a₁^(2*M) := by rw [h0]; ring
    _ = _ := by rw [h1,he,pow_add,pow_add]; ring

lemma twoPole_evaluation_identity {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (r₀ r₁ θ₀ θ₁ : K) (t q b₀ b₁ u₀ : L)
    (h₀ : (t-algebraMap K L r₀)^2*b₀=q-algebraMap K L θ₀)
    (h₁ : (t-algebraMap K L r₁)^2*b₁=q-algebraMap K L θ₁)
    (hu : (t-algebraMap K L r₀)^2*u₀=1)
    (M m N : ℕ) (hm : m ≤ M)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) :
    bivarEvaluation t q (twoPolePolynomial r₀ r₁ θ₀ θ₁ M m N i) =
      ((t-algebraMap K L r₀)^(2*M)*(t-algebraMap K L r₁)^(2*M))*
        twoPoleFunction t (t-algebraMap K L r₀) (t-algebraMap K L r₁) b₀ b₁ u₀ M m N i := by
  cases i with
  | inl j =>
    have hh := (threePole_base_identity (t-algebraMap K L r₀) (t-algebraMap K L r₁) 1
      b₀ (q-algebraMap K L θ₀) t h₀ M m j.val hm).symm
    simp only [twoPolePolynomial,twoPoleFunction,Sum.elim_inl,map_mul,map_pow,map_sub,
      bivarEvaluation_C,bivarEvaluation_X,Polynomial.aeval_X,Polynomial.aeval_C]
    simp only [one_pow,mul_one] at hh
    linear_combination hh
  | inr j =>
    cases j with
    | inl j =>
      have hh := (threePole_extra_identity (t-algebraMap K L r₀) (t-algebraMap K L r₁) 1 b₀ b₁
        (q-algebraMap K L θ₀) (q-algebraMap K L θ₁) h₀ h₁ M m (j.1.val+1) j.2.val hm (by omega)).symm
      simp only [twoPolePolynomial,twoPoleFunction,twoPoleNumerator,Sum.elim_inl,Sum.elim_inr,
        map_mul,map_pow,map_sub,bivarEvaluation_C,bivarEvaluation_X,Polynomial.aeval_X,Polynomial.aeval_C]
      simp only [one_pow,mul_one,pow_add] at hh ⊢
      linear_combination hh
    | inr j =>
      simpa only [twoPolePolynomial,twoPoleFunction,twoPoleNumerator,Sum.elim_inr,
        map_mul,map_pow,map_sub,bivarEvaluation_C,bivarEvaluation_X,Polynomial.aeval_X,Polynomial.aeval_C]
        using (twoPole_extra_right_identity (t-algebraMap K L r₀) (t-algebraMap K L r₁) b₀ u₀
          (q-algebraMap K L θ₀) h₀ hu M m (j.1.val+1) j.2.val hm (by omega)).symm

theorem twoPole_functions_independent {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (r₀ r₁ θ₀ θ₁ : K) (hr : r₀ ≠ r₁) (t q b₀ b₁ u₀ : L)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t)))
    (h₀ : (t-algebraMap K L r₀)^2*b₀=q-algebraMap K L θ₀)
    (h₁ : (t-algebraMap K L r₁)^2*b₁=q-algebraMap K L θ₁)
    (hu : (t-algebraMap K L r₀)^2*u₀=1) (M : ℕ) (N : Fin (M+1) → ℕ) :
    LinearIndependent K (fun i : Σ m : Fin (M+1), Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2)) =>
      twoPoleFunction t (t-algebraMap K L r₀) (t-algebraMap K L r₁) b₀ b₁ u₀ M i.1.val (N i.1) i.2) := by
  let D := (t-algebraMap K L r₀)^(2*M)*(t-algebraMap K L r₁)^(2*M)
  have he := (twoPole_polynomials_independent r₀ r₁ θ₀ θ₁ hr M N).map'
    (bivarEvaluation t q).toLinearMap (LinearMap.ker_eq_bot.mpr (bivarEvaluation_injective t q hi))
  have heq : (fun i : Σ m : Fin (M+1), Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2)) =>
      bivarEvaluation t q (twoPolePolynomial r₀ r₁ θ₀ θ₁ M i.1.val (N i.1) i.2)) =
      (LinearMap.mulLeft K D) ∘ (fun i => twoPoleFunction t (t-algebraMap K L r₀)
        (t-algebraMap K L r₁) b₀ b₁ u₀ M i.1.val (N i.1) i.2) := by
    funext i
    exact twoPole_evaluation_identity r₀ r₁ θ₀ θ₁ t q b₀ b₁ u₀ h₀ h₁ hu M i.1.val (N i.1) (by omega) i.2
  change LinearIndependent K (fun i : Σ m : Fin (M+1), Fin (N m) ⊕ ((Fin m.val × Fin 2) ⊕ (Fin (M-m.val) × Fin 2)) => bivarEvaluation t q (twoPolePolynomial r₀ r₁ θ₀ θ₁ M i.1.val (N i.1) i.2)) at he
  rw [heq] at he
  exact LinearIndependent.of_comp (LinearMap.mulLeft K D) he
end QuarticPowerFree

end OAI
