import Mathlib
import OAI.Algebra.FiniteTensor.MinorReduction

namespace OAI

/-! Algebraic derivatives, minor induction and polynomial Artin approximation. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
variable {K σ : Type*} [Field K] [CharZero K]

 theorem aeval_isAlgebraic {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] {f : S} (hf : IsAlgebraic R f) (P : Polynomial R) :
    IsAlgebraic R (Polynomial.aeval f P) :=
  Algebra.isAlgebraic_adjoin_singleton_iff.mpr hf _ (Polynomial.aeval_mem_adjoin_singleton R f)

 

theorem algebraic_series_pderiv (i : σ) (f : MvPowerSeries σ K)
    (hf : IsAlgebraic (MvPolynomial σ K) f) :
    IsAlgebraic (MvPolynomial σ K) (MvPowerSeries.pderiv i f) := by
  classical
  have hi : Function.Injective (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)) := by
    intro x y h
    apply MvPolynomial.coe_injective σ K
    simpa only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
      MvPowerSeries.map_id,RingHom.id_apply] using h
  obtain ⟨P,_,hP,hD⟩ := exists_relation_derivative_ne_zero hi f hf
  have herr : ∀ Q : Polynomial (MvPolynomial σ K),
      IsAlgebraic (MvPolynomial σ K)
        (MvPowerSeries.pderiv i (Polynomial.aeval f Q)-
          Polynomial.aeval f Q.derivative*MvPowerSeries.pderiv i f) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add Q R hQ hR =>
      have heq : MvPowerSeries.pderiv i (Polynomial.aeval f (Q+R)) -
          Polynomial.aeval f (Q+R).derivative * MvPowerSeries.pderiv i f =
            (MvPowerSeries.pderiv i (Polynomial.aeval f Q) -
              Polynomial.aeval f Q.derivative * MvPowerSeries.pderiv i f) +
            (MvPowerSeries.pderiv i (Polynomial.aeval f R) -
              Polynomial.aeval f R.derivative * MvPowerSeries.pderiv i f) := by
        simp only [map_add,add_mul]
        ring
      rw [heq]
      exact hQ.add hR
    | monomial j a =>
      have ha : IsAlgebraic (MvPolynomial σ K)
          (MvPowerSeries.pderiv i (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K) a)) := by
        simpa only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
          MvPowerSeries.map_id,RingHom.id_apply,MvPowerSeries.pderiv_coe] using
          (isAlgebraic_algebraMap (R:=MvPolynomial σ K) (A:=MvPowerSeries σ K)
            (MvPolynomial.pderiv i a))
      have heq : MvPowerSeries.pderiv i (Polynomial.aeval f (Polynomial.monomial j a)) -
          Polynomial.aeval f (Polynomial.monomial j a).derivative * MvPowerSeries.pderiv i f =
          MvPowerSeries.pderiv i (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K) a) * f^j := by
        simp only [Polynomial.aeval_monomial,Polynomial.derivative_monomial,
          Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,map_mul,map_natCast,
          nsmul_eq_mul]
        ring
      rw [heq]
      exact ha.mul (hf.pow j)
  have hprod : IsAlgebraic (MvPolynomial σ K)
      (Polynomial.aeval f P.derivative*MvPowerSeries.pderiv i f) := by
    simpa only [hP,map_zero,zero_sub,neg_neg] using (herr P).neg
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hD)
    (aeval_isAlgebraic hf _) hprod

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K σ τ : Type*} [Field K] [Finite σ]

 

theorem algebraic_series_rename (j : σ → τ) (hj : Function.Injective j)
    (f : MvPowerSeries σ K) (hf : IsAlgebraic (MvPolynomial σ K) f) :
    IsAlgebraic (MvPolynomial τ K) (MvPowerSeries.rename j f) := by
  apply hf.ringHom_of_comp_eq (MvPolynomial.rename j).toRingHom
    (MvPowerSeries.rename j).toRingHom (MvPolynomial.rename_injective j hj)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,MvPowerSeries.algebraMap_apply',
    Algebra.algebraMap_self,MvPowerSeries.map_id,RingHom.id_apply]
  exact (MvPowerSeries.rename_coe j p).symm

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ : Type*} [Field K] [CharZero K] [Finite τ]

 theorem aeval_minorPolynomial {R A σ ρ : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Fintype σ] [DecidableEq σ]
    (a : (σ ⊕ ρ) → A) (f : σ → MvPolynomial (σ ⊕ ρ) R) :
    aeval a (minorPolynomial f)=Matrix.det (fun k i=>aeval a (pderiv (Sum.inl i) (f k))) := by
  unfold minorPolynomial
  exact RingHom.map_det (aeval a : MvPolynomial (σ ⊕ ρ) R →ₐ[R] A).toRingHom _

 omit [CharZero K] [Finite τ] in
 theorem rename_polynomial_square {υ : Type*} (e : τ ≃ υ) :
    (algebraMap (MvPolynomial υ K) (MvPowerSeries υ K)).comp (MvPolynomial.rename e).toRingHom=
    (MvPowerSeries.renameEquiv K e).toRingHom.comp
      (algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [MvPowerSeries.algebraMap_apply']
  · intro i
    simp [MvPowerSeries.algebraMap_apply']

 

theorem minor_artin_step
    (ih : ∀ p : τ,PolynomialArtinAt K {i : τ // i≠p}) : MinorArtinAt K τ := by
  classical
  intro σ ρ _ _ _ _ f a ha hJ n
  let δ := aeval a (minorPolynomial f)
  have hδ : δ≠0 := by dsimp [δ]; rw [aeval_minorPolynomial]; exact hJ
  by_cases hu : IsUnit δ
  · let F := fun k=>map (algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) (f k)
    have hev (v : (σ ⊕ ρ) → MvPowerSeries τ K) (q : MvPolynomial (σ ⊕ ρ) (MvPolynomial τ K)) :
        eval v (map (algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) q)=aeval v q := by
      rw [←eval₂_eq_eval_map,aeval_def]
    have hFcoeff (k : σ) (d) : IsAlgebraic (MvPolynomial τ K) ((F k).coeff d) := by
      rw [coeff_map]
      exact isAlgebraic_algebraMap _
    have hJF : IsUnit (Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (F k)))) := by
      simp_rw [F,pderiv_map,hev]
      rwa [←aeval_minorPolynomial]
    obtain ⟨b,hb,hbalg,hba⟩ := unit_artin_step F hFcoeff a (fun k=>by rw [hev]; exact ha k) hJF n
    exact ⟨b,fun k=>by rw [←hev]; exact hb k,hbalg,hba⟩
  · have hzero : MvPowerSeries.constantCoeff δ=0 := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero,not_not] at hu
      exact hu
    obtain ⟨p,c,hp,hreg⟩ := exists_regular_linear_chart δ hδ hzero
    let υ := {i : τ // i≠p}
    let e := Equiv.optionSubtypeNe p
    let C := linearSeriesChart p c hp
    let E := C.trans (MvPowerSeries.renameEquiv K e.symm)
    let P := (MvPolynomial.rename e.symm).toRingHom.comp (polynomialChart p c)
    have hsq : (algebraMap (MvPolynomial (Option υ) K) (MvPowerSeries (Option υ) K)).comp P=
        E.toRingHom.comp (algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) := by
      apply RingHom.ext
      intro q
      change (algebraMap (MvPolynomial (Option υ) K) (MvPowerSeries (Option υ) K))
        (MvPolynomial.rename e.symm (polynomialChart p c q))=
        MvPowerSeries.rename e.symm (C ((algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) q))
      have hr := RingHom.congr_fun (rename_polynomial_square (K:=K) e.symm) (polynomialChart p c q)
      have hc := RingHom.congr_fun (polynomialChart_square p c hp) q
      exact hr.trans (congrArg (MvPowerSeries.rename e.symm) hc)
    let f' := fun k=>map P (f k)
    let a' := fun i=>E (a i)
    have hev (v : (σ ⊕ ρ) → MvPowerSeries τ K) (q : MvPolynomial (σ ⊕ ρ) (MvPolynomial τ K)) :
        aeval (fun i=>E (v i)) (map P q)=E (aeval v q) :=
      aeval_map_square P E.toRingHom hsq q v
    have hminor : minorPolynomial f'=map P (minorPolynomial f) := (minorPolynomial_map P f).symm
    obtain ⟨b,hb,hbalg,hba⟩ := option_artin_step (ih p) f' a'
      (fun k=>by rw [hev,ha,map_zero])
      (by
        rw [hminor,hev]
        change MvPowerSeries.subst (axisVars (K:=K) none)
          (MvPowerSeries.rename e.symm (C δ))≠0
        rwa [option_axis_rename])
      (by
        rw [hminor,hev]
        exact fun h=>hu ((isUnit_map_iff E _).mp h)) n
    refine ⟨fun i=>E.symm (b i),?_,?_,?_⟩
    · intro k
      apply E.injective
      rw [map_zero,←hev]
      simpa only [AlgEquiv.apply_symm_apply] using hb k
    · intro i
      change IsAlgebraic (MvPolynomial τ K) (C.symm (MvPowerSeries.rename e (b i)))
      apply algebraic_linearSeriesChart_symm
      exact algebraic_series_rename e e.injective _ (hbalg i)
    · intro i
      have h := series_equiv_jet E.symm.toRingEquiv (hba i)
      change E.symm (b i-a' i)∈_ at h
      simpa only [a',map_sub,AlgEquiv.symm_apply_apply] using h

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
universe u v
variable (K : Type u) [Field K] [CharZero K]

 

theorem polynomial_artin (τ : Type v) [Finite τ] : PolynomialArtinAt K τ := by
  classical
  have h : ∀ n : ℕ,∀ (υ : Type v) [Finite υ],Nat.card υ=n → PolynomialArtinAt K υ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro υ _ hn
      apply polynomial_artin_of_minor
      apply minor_artin_step
      intro p
      have hlt : Nat.card {i : υ // i≠p}<n := by
        let := Fintype.ofFinite υ
        let := Fintype.ofFinite {i : υ // i≠p}
        rw [←hn,←Fintype.card_eq_nat_card,←Fintype.card_eq_nat_card]
        exact Fintype.card_subtype_lt (x:=p) (by simp)
      exact ih _ hlt _ rfl
  exact h _ τ rfl

end
end PD4Tensor.Spreading
end

end OAI
