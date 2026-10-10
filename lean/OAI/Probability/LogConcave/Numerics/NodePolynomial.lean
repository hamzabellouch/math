import Mathlib
import OAI.Probability.LogConcave.Numerics.CompositeAngle

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def zeroNodePolynomial (u : I → ℝ) (i₀ : I) : ℝ[X] :=
  X*∏i∈Finset.univ.erase i₀,(X-C (u i))

lemma zeroNodePolynomial_eval (u : I → ℝ) (i₀ : I) (hu0 : u i₀=0) (j : I) :
    (zeroNodePolynomial u i₀).eval (u j)=0 := by
  by_cases hj : j=i₀
  · simp [hj,hu0,zeroNodePolynomial]
  · simp only [zeroNodePolynomial,eval_mul,eval_X,eval_prod,eval_sub,eval_C]
    have hz : (∏i∈Finset.univ.erase i₀,(u j-u i))=0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩) (sub_self _)
    rw [hz,mul_zero]

lemma zeroNodePolynomial_derivative (u : I → ℝ) (i₀ : I) :
    (zeroNodePolynomial u i₀).derivative.eval 0=∏i∈Finset.univ.erase i₀,-u i := by
  simp only [zeroNodePolynomial,derivative_mul,derivative_X,eval_add,eval_mul,eval_X,one_mul,zero_mul,add_zero]
  simp only [eval_prod,eval_sub,eval_X,eval_C,zero_sub]

lemma zeroNodePolynomial_derivative_ne (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) : (zeroNodePolynomial u i₀).derivative.eval 0≠0 := by
  rw [zeroNodePolynomial_derivative]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (fun hz => (Finset.mem_erase.mp hi).1 (hu (hz.trans hu0.symm)))

def zeroHermiteBasis (u : I → ℝ) (i₀ i : I) : ℝ[X] :=
  Lagrange.basis Finset.univ u i-
    C (derivativeWeight u i/(zeroNodePolynomial u i₀).derivative.eval 0)*zeroNodePolynomial u i₀

lemma zeroHermiteBasis_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i j : I) :
    (zeroHermiteBasis u i₀ i).eval (u j)=if i=j then 1 else 0 := by
  simp only [zeroHermiteBasis,eval_sub,eval_mul,eval_C,zeroNodePolynomial_eval u i₀ hu0 j,mul_zero,sub_zero]
  by_cases h : i=j
  · subst i
    simp only [ite_true]
    exact Lagrange.eval_basis_self hu.injOn (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

lemma zeroHermiteBasis_derivative_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i : I) :
    (zeroHermiteBasis u i₀ i).derivative.eval 0=0 := by
  simp only [zeroHermiteBasis,derivative_sub,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_sub,eval_mul,eval_C]
  change derivativeWeight u i-(derivativeWeight u i/(zeroNodePolynomial u i₀).derivative.eval 0)*
    (zeroNodePolynomial u i₀).derivative.eval 0=0
  rw [div_mul_cancel₀ _ (zeroNodePolynomial_derivative_ne u hu i₀ hu0),sub_self]

def zeroHermitePolynomial (u : I → ℝ) (i₀ : I) (v : I → ℝ) : ℝ[X] :=
  ∑i,C (v i)*zeroHermiteBasis u i₀ i

lemma zeroHermitePolynomial_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → ℝ) (j : I) :
    (zeroHermitePolynomial u i₀ v).eval (u j)=v j := by
  simp only [zeroHermitePolynomial,eval_finsetSum,eval_mul,eval_C,zeroHermiteBasis_eval u hu i₀ hu0]
  simp

lemma zeroHermitePolynomial_derivative_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → ℝ) :
    (zeroHermitePolynomial u i₀ v).derivative.eval 0=0 := by
  simp only [zeroHermitePolynomial,derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_finsetSum,eval_mul,eval_C,zeroHermiteBasis_derivative_zero u hu i₀ hu0,mul_zero,Finset.sum_const_zero]

lemma polynomial_divX_eval {p : ℝ[X]} (hp : p.eval 0=0) {z : ℝ} (hz : z≠0) :
    p.divX.eval z=p.eval z/z := by
  have hp0 : p.coeff 0=0 := (coeff_zero_eq_eval_zero p).trans hp
  have hh := congrArg (fun q : ℝ[X] => q.eval z) (X_mul_divX_add p)
  simp only [eval_add,eval_mul,eval_X,eval_C,hp0,add_zero] at hh
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using hh

def zeroHermiteRegularized (u : I → ℝ) (i₀ i : I) : ℝ[X] :=
  (zeroHermiteBasis u i₀ i).derivative.divX

lemma zeroHermiteRegularized_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i : I) {z : ℝ} (hz : z≠0) :
    (zeroHermiteRegularized u i₀ i).eval z=(zeroHermiteBasis u i₀ i).derivative.eval z/z :=
  polynomial_divX_eval (zeroHermiteBasis_derivative_zero u hu i₀ hu0 i) hz

def zeroHermiteWeight (u : I → ℝ) (i₀ i : I) : ℝ :=
  ∫z in (0:ℝ)..1,(zeroHermiteRegularized u i₀ i).eval z

lemma zeroHermite_weight_finite (u : I → ℝ) (i₀ i : I) :
    IntervalIntegrable (fun z => (zeroHermiteRegularized u i₀ i).eval z) volume 0 1 :=
  (Polynomial.continuous _).intervalIntegrable 0 1

lemma zeroHermite_weights_abs (u : I → ℝ) (i₀ : I) {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∑i,|zeroHermiteWeight u i₀ i/ℓ|)=(∑i,|zeroHermiteWeight u i₀ i|)/ℓ := by
  simp only [abs_div,abs_of_pos hℓ,Finset.sum_div]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma zeroNodePolynomial_natDegree (u : I → ℝ) (i₀ : I) :
    (zeroNodePolynomial u i₀).natDegree≤Fintype.card I := by
  have hI : 0<Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hp := natDegree_prod_le (Finset.univ.erase i₀) (fun i => (X-C (u i):ℝ[X]))
  simp only [natDegree_X_sub_C,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i₀),
    Finset.card_univ,Nat.nsmul_eq_mul,mul_one] at hp
  have hm := natDegree_mul_le (p:=(X:ℝ[X])) (q:=∏i∈Finset.univ.erase i₀,(X-C (u i)))
  change (zeroNodePolynomial u i₀).natDegree≤_ at hm
  simp only [natDegree_X] at hm
  exact hm.trans (by omega)

lemma zeroHermiteBasis_natDegree (u : I → ℝ) (hu : Function.Injective u) (i₀ i : I) :
    (zeroHermiteBasis u i₀ i).natDegree≤Fintype.card I := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · rw [Lagrange.natDegree_basis hu.injOn (Finset.mem_univ i),Finset.card_univ]
    omega
  · exact (natDegree_C_mul_le _ _).trans (zeroNodePolynomial_natDegree u i₀)

lemma zeroHermitePolynomial_degree (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (v : I → ℝ) :
    (zeroHermitePolynomial u i₀ v).degree≤Fintype.card I := by
  apply (degree_sum_le _ _).trans
  exact Finset.sup_le (fun i _ => degree_le_of_natDegree_le
    ((natDegree_C_mul_le _ _).trans (zeroHermiteBasis_natDegree u hu i₀ i)))

lemma zeroHermite_unique_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (p : ℝ[X])
    (hp : p.degree≤Fintype.card I) (hpder : p.derivative.eval 0=0)
    (hpval : ∀i,p.eval (u i)=0) : p=0 := by
  by_contra hpne
  have hp0 : p.eval 0=0 := by simpa only [hu0] using hpval i₀
  have hp1 : p.coeff 1=0 := by
    simpa only [←coeff_zero_eq_eval_zero,coeff_derivative,Nat.cast_zero,zero_add,mul_one] using hpder
  have hqval (i : I) : p.divX.eval (u i)=0 := by
    by_cases hi : i=i₀
    · subst i
      rw [hu0,←coeff_zero_eq_eval_zero,coeff_divX]
      exact hp1
    · have hn : u i≠0 := fun h => hi (hu (h.trans hu0.symm))
      rw [polynomial_divX_eval hp0 hn,hpval i,zero_div]
  have hqdegree := (degree_divX_lt hpne).trans_le hp
  have he := Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn
    (by simpa only [Finset.card_univ] using hqdegree)
  have hqzero : p.divX=0 := by
    rw [he]
    simp only [Lagrange.interpolate_apply,hqval,C_0,zero_mul,Finset.sum_const_zero]
  have heq := divX_eq_zero_iff.mp hqzero
  have hpc0 := (coeff_zero_eq_eval_zero p).trans hp0
  rw [hpc0,C_0] at heq
  exact hpne heq

theorem zeroHermite_reproduces (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (p : ℝ[X])
    (hp : p.degree≤Fintype.card I) (hpder : p.derivative.eval 0=0) :
    zeroHermitePolynomial u i₀ (fun i => p.eval (u i))=p := by
  apply sub_eq_zero.mp
  apply zeroHermite_unique_zero u hu i₀ hu0
  · exact (degree_sub_le _ _).trans (max_le (zeroHermitePolynomial_degree u hu i₀ _) hp)
  · simp only [derivative_sub,eval_sub,zeroHermitePolynomial_derivative_zero u hu i₀ hu0,hpder,sub_self]
  · intro i
    simp only [eval_sub,zeroHermitePolynomial_eval u hu i₀ hu0,sub_self]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω] {μ : Measure Ω}

def zeroHermiteInterpolation (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) : E :=
  ∑i,(zeroHermiteBasis u i₀ i).eval t • v i

def zeroHermiteAction (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) : E :=
  ∑i,(zeroHermiteRegularized u i₀ i).eval t • v i

lemma zeroHermiteInterpolation_hasDerivAt (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) :
    HasDerivAt (zeroHermiteInterpolation u i₀ v)
      (∑i,(zeroHermiteBasis u i₀ i).derivative.eval t • v i) t := by
  exact HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => ((zeroHermiteBasis u i₀ i).hasDerivAt t).smul_const (v i))

lemma zeroHermiteInterpolation_derivative_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → E) :
    HasDerivAt (zeroHermiteInterpolation u i₀ v) 0 0 := by
  simpa only [zeroHermiteBasis_derivative_zero u hu i₀ hu0,zero_smul,Finset.sum_const_zero]
    using zeroHermiteInterpolation_hasDerivAt u i₀ v 0

lemma zeroHermiteAction_continuous (u : I → ℝ) (i₀ : I) (v : I → E) :
    Continuous (zeroHermiteAction u i₀ v) :=
  continuous_finsetSum _ (fun _ _ => (Polynomial.continuous _).smul continuous_const)

lemma zeroHermiteAction_eq (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → E) {t : ℝ} (ht : t≠0) :
    zeroHermiteAction u i₀ v t=t⁻¹ • deriv (zeroHermiteInterpolation u i₀ v) t := by
  rw [(zeroHermiteInterpolation_hasDerivAt u i₀ v t).deriv]
  simp only [zeroHermiteAction,zeroHermiteRegularized_eval u hu i₀ hu0 _ ht,
    Finset.smul_sum,smul_smul,div_eq_mul_inv,mul_comm]

lemma zeroHermiteAction_integral [CompleteSpace E] (u : I → ℝ) (i₀ : I) (v : I → E) :
    (∫t in (0:ℝ)..1,zeroHermiteAction u i₀ v t)=∑i,zeroHermiteWeight u i₀ i • v i := by
  unfold zeroHermiteAction
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_smul_const _ _
  · intro i _
    exact ((Polynomial.continuous _).smul continuous_const).intervalIntegrable 0 1

theorem zeroHermiteAction_value_error_rms (u : I → ℝ) (i₀ : I)
    (v w : I → Ω → E) {ℓ B : ℝ} (hℓ : 0<ℓ)
    (hm : ∀i,AEStronglyMeasurable (fun z => v i z-w i z) μ)
    (hi : ∀i,Integrable (fun z => ‖v i z-w i z‖^2) μ)
    (hB : ∀i,(∫z,‖v i z-w i z‖^2 ∂μ)≤B) :
    let err := fun z => (∑i,(zeroHermiteWeight u i₀ i/ℓ) • v i z)-
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • w i z
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤((∑i,|zeroHermiteWeight u i₀ i|)/ℓ)^2*B := by
  dsimp only
  have he (z : Ω) : (∑i,(zeroHermiteWeight u i₀ i/ℓ) • v i z)-
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • w i z=
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • (v i z-w i z) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
  simp_rw [he]
  simpa only [zeroHermite_weights_abs u i₀ hℓ] using
    RMSIntegral.weighted_sum_sq (fun i => zeroHermiteWeight u i₀ i/ℓ)
      (fun i z => v i z-w i z) hm hi hB
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma zeroHermite_reproduces_power (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (k : ℕ) (hk : k≤Fintype.card I) (hk1 : k≠1) (t : ℝ) :
    (∑i,(zeroHermiteBasis u i₀ i).eval t*(u i)^k)=t^k := by
  have hd : ((X:ℝ[X])^k).derivative.eval 0=0 := by
    rcases k with _|k
    · simp
    rcases k with _|k
    · exact (hk1 rfl).elim
    · simp
  have hh := congrArg (fun p : ℝ[X] => p.eval t)
    (zeroHermite_reproduces u hu i₀ hu0 (X^k) (by simpa using hk) hd)
  simpa only [zeroHermitePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,mul_comm] using hh

theorem zeroHermite_reproduces_vector (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hn : 1≤n) (hcard : n≤Fintype.card I)
    (v : Fin (n+1) → E) (hv : v ⟨1,by omega⟩=0) (t : ℝ) :
    zeroHermiteInterpolation u i₀ (fun i => ∑k : Fin (n+1),(u i)^(k:ℕ) • v k) t=
      ∑k : Fin (n+1),t^(k:ℕ) • v k := by
  unfold zeroHermiteInterpolation
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (k:ℕ)=1
  · have he : k=⟨1,by omega⟩ := Fin.ext hk
    simp only [he,hv,smul_zero,Finset.sum_const_zero]
  · rw [←Finset.sum_smul,zeroHermite_reproduces_power u hu i₀ hu0 k (by omega) hk]

lemma zeroHermite_reproduces_chainTaylor (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hn : 1≤n) (hcard : n≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJ : J 1 0=0) (ℓ t : ℝ) :
    zeroHermiteInterpolation u i₀ (fun i => chainTaylor J n 0 (ℓ*u i)) t=
      chainTaylor J n 0 (ℓ*t) := by
  have he (v : ℝ) := chainTaylor_scaled_eval J n 0 ℓ v
  simp only [zero_add] at he
  simp_rw [he]
  apply zeroHermite_reproduces_vector u hu i₀ hu0 n hn hcard
  simp only [hJ,smul_zero]

lemma zeroHermiteInterpolation_sub (u : I → ℝ) (i₀ : I) (v w : I → E) (t : ℝ) :
    zeroHermiteInterpolation u i₀ (fun i => v i-w i) t=
      zeroHermiteInterpolation u i₀ v t-zeroHermiteInterpolation u i₀ w t := by
  simp only [zeroHermiteInterpolation,smul_sub,Finset.sum_sub_distrib]

theorem zeroHermite_chain_error_eq (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hn : 1≤n) (hcard : n≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJ : J 1 0=0) (ℓ t : ℝ) :
    J 0 (ℓ*t)-zeroHermiteInterpolation u i₀ (fun i => J 0 (ℓ*u i)) t=
      (J 0 (ℓ*t)-chainTaylor J n 0 (ℓ*t))-
        zeroHermiteInterpolation u i₀ (fun i => J 0 (ℓ*u i)-chainTaylor J n 0 (ℓ*u i)) t := by
  rw [zeroHermiteInterpolation_sub,zeroHermite_reproduces_chainTaylor u hu i₀ hu0 n hn hcard J hJ]
  abel
end LogConcaveSampling.Quadrature

end

end

end

end OAI
