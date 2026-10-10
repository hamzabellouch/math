import Mathlib
import OAI.Algebra.FiniteTensor.JetTopology

namespace OAI

/-! Lower and regular coefficients in prepared polynomial systems. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ σ κ : Type*} [Field K] [Finite τ]
  [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

 

omit [DecidableEq σ] [DecidableEq κ] in
theorem lower_coefficient_prepared
    (ih : PolynomialArtinAt K τ)
    (f : κ → MvPolynomial σ (Polynomial (MvPolynomial τ K)))
    (D : MvPolynomial σ (Polynomial (MvPolynomial τ K)))
    (a : σ → PowerSeries (MvPowerSeries τ K))
    (ha : ∀ k,eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) (f k))=0)
    (h : Polynomial (MvPowerSeries τ K))
    (hh : h.IsDistinguishedAt (jetIdeal (K:=K) (σ:=τ)))
    (hjac : (h : PowerSeries (MvPowerSeries τ K))∈
      Ideal.jacobson (⊥ : Ideal (PowerSeries (MvPowerSeries τ K))))
    (u : PowerSeries (MvPowerSeries τ K)) (hu : IsUnit u)
    (hD : eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) D)=(h : PowerSeries (MvPowerSeries τ K))*u)
    (N : ℕ) (hN : 0<N) :
    ∃ b : σ → PowerSeries (MvPowerSeries τ K),
      (∀ i,IsAlgebraic (Polynomial (MvPolynomial τ K)) (b i)) ∧
      (eval b (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) D)≠0) ∧
      (∀ k,eval b (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) D)^2∣eval b
          (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=MvPowerSeries τ K)) (f k))) ∧
      ∀ i,(MvPowerSeries.optionEquivLeft τ K).symm (b i-a i)∈
        (jetIdeal (K:=K) (σ:=Option τ))^N := by
  let A := MvPowerSeries τ K
  let B := MvPolynomial τ K
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let φ : Polynomial B →+* Polynomial A := Polynomial.mapRingHom (algebraMap B A)
  let fA := fun k=>map φ (f k)
  let DA := map φ D
  have hev (p : MvPolynomial σ (Polynomial B)) (v : σ → PowerSeries A) :
      eval₂ Polynomial.coeToPowerSeries.ringHom v (map φ p)=
        eval v (map (seriesCoefficientMap (B:=B) (A:=A)) p) := by
    rw [eval₂_map,←eval₂_eq_eval_map]
  obtain ⟨r,q,k,w,har,hfr,hDr,hw⟩ := finite_weierstrass_unit_constraints
    (jetIdeal (K:=K) (σ:=τ)) h hh hjac a fA (fun k=>by rw [hev]; exact ha k)
    DA u hu (by rw [hev]; exact hD)
  let p := remainderPoint h r k w
  have hp : ∀ e,eval₂ (Polynomial.mapRingHom (algebraMap B A)) p
      (remainderEquation f D e)=0 := by
    apply (remainder_equations_iff _ f D h r k w).mpr
    constructor
    · intro j
      simpa only [fA,eval_map] using hfr j
    · simpa only [DA,eval_map] using hDr
  have hcoeff := coefficient_equations_original (algebraMap B A) p (remainderEquation f D) hp
  obtain ⟨x,hx,hxalg,hxclose⟩ := ih.finite (coefficientEquation p (remainderEquation f D))
    (coefficientPoint p) hcoeff N
  let E := MvPowerSeries.optionEquivLeft τ K
  let q' : σ → PowerSeries A := fun i=>E (MvPowerSeries.truncTotal N (E.symm (q i)))
  have hq' (i : σ) : IsAlgebraic (Polynomial B) (q' i) := by
    apply algebraic_option_series
    exact isAlgebraic_algebraMap (MvPowerSeries.truncTotal N (E.symm (q i)))
  obtain ⟨b,hb,hbn,hbd,hbc⟩ := coefficient_prepared_point
    ((jetIdeal (K:=K) (σ:=τ))^N) (jetIdeal_pow_le_jacobson N hN)
    f D p hh.monic hjac hw x hxalg hxclose hx q' hq'
  refine ⟨b,hb,hbn,hbd,fun i=>?_⟩
  let J := (jetIdeal (K:=K) (σ:=Option τ))^N
  have hc : E.symm (b i-((r i : PowerSeries A)+(h : PowerSeries A)^2*q' i))∈J :=
    option_inverse_coefficient_jet (hbc i)
  have hqclose : E.symm (q' i-q i)∈J := by
    rw [map_sub]
    change E.symm (E (MvPowerSeries.truncTotal N (E.symm (q i))))-E.symm (q i)∈J
    rw [AlgEquiv.symm_apply_apply]
    exact truncate_close_jetIdeal _ N
  have hsecond : E.symm (((r i : PowerSeries A)+(h : PowerSeries A)^2*q' i)-a i)∈J := by
    rw [har i]
    have he : ((r i : PowerSeries A)+(h : PowerSeries A)^2*q' i)-
        ((r i : PowerSeries A)+(h : PowerSeries A)^2*q i)=
          (h : PowerSeries A)^2*(q' i-q i) := by ring
    rw [he,map_mul,map_pow]
    exact J.mul_mem_left _ hqclose
  have hs := J.add_mem hc hsecond
  rw [←map_add] at hs
  change E.symm (b i-a i)∈J
  convert hs using 1
  abel_nf

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ σ κ : Type*} [Field K] [Finite τ]
  [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

 

omit [DecidableEq σ] [DecidableEq κ] in
theorem regular_coefficient_prepared
    (ih : PolynomialArtinAt K τ)
    (f : κ → MvPolynomial σ (Polynomial (MvPolynomial τ K)))
    (D : MvPolynomial σ (Polynomial (MvPolynomial τ K)))
    (a : σ → PowerSeries (MvPowerSeries τ K))
    (ha : ∀ k,eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) (f k))=0)
    (hreg : (eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) D)).map (IsLocalRing.residue (MvPowerSeries τ K))≠0)
    (hnonunit : ¬IsUnit (eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) D)))
    (N : ℕ) (hN : 0<N) :
    ∃ b : σ → PowerSeries (MvPowerSeries τ K),
      (∀ i,IsAlgebraic (Polynomial (MvPolynomial τ K)) (b i)) ∧
      (eval b (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) D)≠0) ∧
      (∀ k,eval b (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) D)^2∣eval b
          (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=MvPowerSeries τ K)) (f k))) ∧
      ∀ i,(MvPowerSeries.optionEquivLeft τ K).symm (b i-a i)∈
        (jetIdeal (K:=K) (σ:=Option τ))^N := by
  let A := MvPowerSeries τ K
  let : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    rw [←jetIdeal_eq_maximalIdeal]
    infer_instance
  let δ := eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=A)) D)
  let h := δ.weierstrassDistinguished hreg
  let u := δ.weierstrassUnit hreg
  have hu : IsUnit u := δ.isUnit_weierstrassUnit hreg
  have he : δ=(h : PowerSeries A)*u := δ.eq_weierstrassDistinguished_mul_weierstrassUnit hreg
  have hh : h.IsDistinguishedAt (jetIdeal (K:=K) (σ:=τ)) := by
    rw [jetIdeal_eq_maximalIdeal]
    exact δ.isDistinguishedAt_weierstrassDistinguished hreg
  have hn : ¬IsUnit (h : PowerSeries A) := by
    intro ht
    apply hnonunit
    change IsUnit δ
    rw [he]
    exact ht.mul hu
  have hj : (h : PowerSeries A)∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)) := by
    apply IsLocalRing.maximalIdeal_le_jacobson _
    rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
    exact hn
  exact lower_coefficient_prepared ih f D a ha h hh hj u hu he N hN

end
end PD4Tensor.Spreading
end

end OAI
