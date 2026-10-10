import Mathlib
import OAI.Algebra.FiniteTensor.LinearCharts
import OAI.Algebra.FiniteTensor.PreparedApproximation

namespace OAI

/-! Artin induction steps for distinguished and unit equations. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ σ ρ : Type*} [Field K] [Finite τ] [DecidableEq τ]
  [Fintype σ] [DecidableEq σ] [Fintype ρ] [DecidableEq ρ]

 omit [Finite τ] [DecidableEq τ] in
 theorem seriesCoefficientMap_eq_algebraMap :
    seriesCoefficientMap (B:=MvPolynomial τ K) (A:=MvPowerSeries τ K)=
      algebraMap (Polynomial (MvPolynomial τ K)) (PowerSeries (MvPowerSeries τ K)) := by
  apply Polynomial.ringHom_ext
  · intro p
    simp [seriesCoefficientMap,PowerSeries.algebraMap_apply']
  · simp [seriesCoefficientMap,PowerSeries.algebraMap_apply']

 theorem aeval_map_square {R S A B χ : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (φ : R →+* S) (E : A →+* B)
    (hsq : (algebraMap S B).comp φ=E.comp (algebraMap R A))
    (f : MvPolynomial χ R) (a : χ → A) :
    aeval (fun i=>E (a i)) (map φ f)=E (aeval a f) := by
  rw [aeval_def,eval₂_map,aeval_def]
  rw [hsq]
  exact (hom_eval₂ f (algebraMap R A) E a).symm

 

omit [DecidableEq ρ] in
theorem option_artin_step
    (ih : PolynomialArtinAt K τ)
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPolynomial (Option τ) K))
    (a : (σ ⊕ ρ) → MvPowerSeries (Option τ) K)
    (ha : ∀ k,aeval a (f k)=0)
    (hreg : MvPowerSeries.subst (axisVars (K:=K) none) (aeval a (minorPolynomial f))≠0)
    (hnonunit : ¬IsUnit (aeval a (minorPolynomial f))) (n : ℕ) :
    ∃ b : (σ ⊕ ρ) → MvPowerSeries (Option τ) K,
      (∀ k,aeval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial (Option τ) K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=Option τ))^n := by
  classical
  let E := MvPowerSeries.optionEquivLeft τ K
  let P := MvPolynomial.optionEquivLeft K τ
  let f' := fun k=>map P.toRingHom (f k)
  let a' := fun i=>E (a i)
  have hev (q : MvPolynomial (σ ⊕ ρ) (MvPolynomial (Option τ) K))
      (v : (σ ⊕ ρ) → MvPowerSeries (Option τ) K) :
      eval (fun i=>E (v i)) (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) (map P.toRingHom q))=E (aeval v q) := by
    rw [seriesCoefficientMap_eq_algebraMap,←eval₂_eq_eval_map,←aeval_def]
    exact aeval_map_square P.toRingHom E.toRingHom option_series_polynomial_square.symm q v
  have hminor : minorPolynomial f'=map P.toRingHom (minorPolynomial f) :=
    (minorPolynomial_map P.toRingHom f).symm
  obtain ⟨b,hb,hbalg,hba⟩ := aligned_artin_step ih f' a'
    (fun k=>by rw [hev,ha,map_zero])
    (by
      rw [hminor,hev]
      apply residue_regular_of_constant_regular
      rwa [←option_axis_constant])
    (by
      rw [hminor,hev]
      exact fun hu=>hnonunit ((isUnit_map_iff E _).mp hu)) n
  refine ⟨fun i=>E.symm (b i),?_,fun i=>algebraic_option_series_symm (hbalg i),?_⟩
  · intro k
    apply E.injective
    rw [map_zero,←hev]
    simpa only [AlgEquiv.apply_symm_apply] using hb k
  · intro i
    simpa only [a',E,map_sub,AlgEquiv.symm_apply_apply] using hba i

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ σ ρ : Type*} [Field K] [Finite τ]
  [Fintype σ] [DecidableEq σ] [Fintype ρ] [DecidableEq ρ]

 

omit [Fintype ρ] [DecidableEq ρ] in
theorem unit_artin_step
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a : (σ ⊕ ρ) → MvPowerSeries τ K) (ha : ∀ k,eval a (f k)=0)
    (hunit : IsUnit (Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))))
    (n : ℕ) :
    ∃ b : (σ ⊕ ρ) → MvPowerSeries τ K,(∀ k,eval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  classical
  let δ := Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))
  let N := 2*δ.order.toNat+n+1
  let u := fun i=>(MvPowerSeries.truncTotal N (a i):MvPowerSeries τ K)
  have hc (i) : u i-a i∈(jetIdeal (K:=K) (σ:=τ))^N := truncate_close_jetIdeal _ _
  have hN : 1≤N := by dsimp [N]; omega
  have hd : Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))-δ∈
      jetIdeal (K:=K) (σ:=τ) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    dsimp only [δ]
    rw [map_sub,sub_eq_zero]
    erw [RingHom.map_det,RingHom.map_det]
    congr 1
    ext row column
    apply Ideal.Quotient.eq.mpr
    apply mv_eval_sub_mem
    intro index
    simpa using Ideal.pow_le_pow_right hN (hc index)
  have hcc : MvPowerSeries.constantCoeff
      (Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k))))=
      MvPowerSeries.constantCoeff δ := by
    have hd' : Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))-δ∈
        (jetIdeal (K:=K) (σ:=τ))^1 := by simpa only [pow_one] using hd
    have hz := (mem_jetIdeal_pow_iff_coeff _ 1).mp hd' 0 (by simp)
    simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff,map_sub,sub_eq_zero] using hz
  have hu : IsUnit (Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,hcc]
    exact MvPowerSeries.isUnit_iff_constantCoeff.mp hunit
  obtain ⟨b,hb,hbalg,hfree,hba⟩ := fixed_jet_prepared_approximation f hcoeff a u ha
    (fun i=>isAlgebraic_algebraMap (MvPowerSeries.truncTotal N (a (Sum.inr i)))) n
    hunit.ne_zero hc (fun k=>(hu.pow 2).dvd)
  exact ⟨b,hb,hbalg,hba⟩

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial
variable {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A]

 
theorem polynomial_remove_X_factor {R : Type*} [Semiring R]
    (p : Polynomial R) (hp : p≠0) :
    ∃ (n : ℕ) (q : Polynomial R),p=X^n*q ∧ q.coeff 0≠0 := by
  obtain ⟨q,hq⟩ := (X_pow_dvd_iff.mpr
    (fun d hd=>coeff_eq_zero_of_lt_natTrailingDegree hd) : X^p.natTrailingDegree∣p)
  refine ⟨p.natTrailingDegree,q,hq,?_⟩
  have he : (X^p.natTrailingDegree*q).coeff p.natTrailingDegree=q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul q p.natTrailingDegree 0
  rw [←hq] at he
  rw [←he]
  exact trailingCoeff_nonzero_iff_nonzero.mpr hp

end
end PD4Tensor.Spreading
end

end OAI
