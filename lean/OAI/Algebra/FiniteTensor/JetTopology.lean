import Mathlib
import OAI.Algebra.FiniteTensor.WeierstrassConstraints

namespace OAI

/-! Jet ideals, completion and finite polynomial approximation statements. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ : Type*} [CommRing K] [Finite σ]

abbrev jetIdeal : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)

 theorem map_jetIdeal_completion :
    Ideal.map (toAdicCompletionAlgEquiv σ K).toRingEquiv (jetIdeal (K:=K) (σ:=σ)) =
      (MvPolynomial.idealOfVars σ K).map
        (algebraMap (MvPolynomial σ K)
          (AdicCompletion (MvPolynomial.idealOfVars σ K) (MvPolynomial σ K))) := by
  simp_rw [jetIdeal,MvPolynomial.idealOfVars,Ideal.map_span,←Set.range_comp]
  congr 2
  ext i
  simp [AdicCompletion.algebraMap_apply,←MvPolynomial.coe_X,toAdicCompletion_coe]

 theorem jetIdeal_power_completion (n : ℕ) :
    ((jetIdeal (K:=K) (σ:=σ))^n).map (toAdicCompletionAlgEquiv σ K).toRingEquiv =
      ((MvPolynomial.idealOfVars σ K)^n).map
        (algebraMap (MvPolynomial σ K)
          (AdicCompletion (MvPolynomial.idealOfVars σ K) (MvPolynomial σ K))) := by
  rw [Ideal.map_pow,map_jetIdeal_completion,Ideal.map_pow]

 theorem mem_completion_power_iff (f : MvPowerSeries σ K) (n : ℕ) :
    toAdicCompletion σ K f∈((MvPolynomial.idealOfVars σ K)^n).map
        (algebraMap (MvPolynomial σ K)
          (AdicCompletion (MvPolynomial.idealOfVars σ K) (MvPolynomial σ K))) ↔
      ∀ d,Finsupp.degree d<n → coeff d f=0 := by
  have hk := AdicCompletion.pow_smul_top_eq_ker_eval
    (M:=MvPolynomial σ K) (n:=n) (MvPolynomial.idealOfVars_fg σ K)
  rw [Ideal.smul_top_eq_map] at hk
  change toAdicCompletion σ K f∈
    (((MvPolynomial.idealOfVars σ K)^n).map
      (algebraMap (MvPolynomial σ K)
        (AdicCompletion (MvPolynomial.idealOfVars σ K) (MvPolynomial σ K)))).restrictScalars
      (MvPolynomial σ K) ↔ _
  rw [hk,LinearMap.mem_ker]
  rw [AdicCompletion.eval_apply,toAdicCompletion_apply_eq_mk_truncTotal]
  rw [Ideal.Quotient.eq_zero_iff_mem,smul_eq_mul,Ideal.mul_top,
    MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall_congr' fun d=>imp_congr_right fun hd=>by rw [coeff_truncTotal _ hd]

 theorem mem_jetIdeal_pow_iff_coeff (f : MvPowerSeries σ K) (n : ℕ) :
    f∈(jetIdeal (K:=K) (σ:=σ))^n ↔ ∀ d,Finsupp.degree d<n → coeff d f=0 := by
  rw [←mem_completion_power_iff,←jetIdeal_power_completion]
  exact (Ideal.apply_mem_of_equiv_iff
    (f:=(toAdicCompletionAlgEquiv σ K).toRingEquiv)).symm

 theorem mem_jetIdeal_pow_iff_order (f : MvPowerSeries σ K) (n : ℕ) :
    f∈(jetIdeal (K:=K) (σ:=σ))^n ↔ (n : ℕ∞)≤f.order := by
  rw [mem_jetIdeal_pow_iff_coeff]
  constructor
  · exact nat_le_order
  · intro h d hd
    exact coeff_of_lt_order ((WithTop.coe_lt_coe.mpr hd).trans_le h)

 theorem truncate_close_jetIdeal (f : MvPowerSeries σ K) (n : ℕ) :
    (truncTotal n f : MvPowerSeries σ K)-f∈(jetIdeal (K:=K) (σ:=σ))^n := by
  rw [mem_jetIdeal_pow_iff_coeff]
  intro d hd
  rw [map_sub,MvPolynomial.coeff_coe,coeff_truncTotal _ hd,sub_self]

end
section Domain
variable {K σ : Type*} [CommRing K] [IsDomain K] [Finite σ]

 

 theorem quotient_jet_control {d q : MvPowerSeries σ K} (hd : d≠0) (n : ℕ)
    (h : d*q∈(jetIdeal (K:=K) (σ:=σ))^(d.order.toNat+n)) :
    q∈(jetIdeal (K:=K) (σ:=σ))^n := by
  by_cases hq : q=0
  · simp [hq]
  rw [mem_jetIdeal_pow_iff_order] at h ⊢
  have hod := (MvPowerSeries.ne_zero_iff_order_finite.mp hd).symm
  have hoq := (MvPowerSeries.ne_zero_iff_order_finite.mp hq).symm
  rw [MvPowerSeries.order_mul,hod,hoq] at h
  have hn : d.order.toNat+n≤d.order.toNat+q.order.toNat := by exact_mod_cast h
  rw [hoq]
  exact_mod_cast (show n≤q.order.toNat by omega)

 

 theorem high_order_not_divisibility (N : ℕ) :
    (MvPowerSeries.X true : MvPowerSeries Bool ℚ)^N∈(jetIdeal (K:=ℚ) (σ:=Bool))^N ∧
      ¬(MvPowerSeries.X false : MvPowerSeries Bool ℚ)^2∣(MvPowerSeries.X true)^N := by
  constructor
  · exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self true)) N
  · intro h
    have hz := MvPowerSeries.X_pow_dvd_iff.mp h (Finsupp.single true N) (by simp)
    simp [MvPowerSeries.coeff_X_pow] at hz

end Domain
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K τ : Type*} [CommRing K]

 
theorem option_series_polynomial_square :
    (MvPowerSeries.optionEquivLeft τ K).toRingHom.comp
      (algebraMap (MvPolynomial (Option τ) K) (MvPowerSeries (Option τ) K))=
    (algebraMap (Polynomial (MvPolynomial τ K)) (PowerSeries (MvPowerSeries τ K))).comp
      (MvPolynomial.optionEquivLeft K τ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [MvPolynomial.optionEquivLeft_C,MvPowerSeries.algebraMap_apply',
      PowerSeries.algebraMap_apply']
  · intro i
    cases i <;> simp [MvPowerSeries.algebraMap_apply',PowerSeries.algebraMap_apply']

 theorem option_series_polynomial_square_symm :
    (MvPowerSeries.optionEquivLeft τ K).symm.toRingHom.comp
      (algebraMap (Polynomial (MvPolynomial τ K)) (PowerSeries (MvPowerSeries τ K)))=
    (algebraMap (MvPolynomial (Option τ) K) (MvPowerSeries (Option τ) K)).comp
      (MvPolynomial.optionEquivLeft K τ).symm.toRingHom := by
  apply RingHom.ext
  intro p
  apply (MvPowerSeries.optionEquivLeft τ K).injective
  have h := RingHom.congr_fun (option_series_polynomial_square (K:=K) (τ:=τ))
    ((MvPolynomial.optionEquivLeft K τ).symm p)
  change (MvPowerSeries.optionEquivLeft τ K)
    ((MvPowerSeries.optionEquivLeft τ K).symm ((algebraMap _ _) p))=_
  rw [AlgEquiv.apply_symm_apply]
  change (MvPowerSeries.optionEquivLeft τ K)
    ((algebraMap _ _) ((MvPolynomial.optionEquivLeft K τ).symm p))=
      (algebraMap _ _) ((MvPolynomial.optionEquivLeft K τ)
        ((MvPolynomial.optionEquivLeft K τ).symm p)) at h
  change (algebraMap (Polynomial (MvPolynomial τ K)) (PowerSeries (MvPowerSeries τ K))) p=
    (MvPowerSeries.optionEquivLeft τ K) ((algebraMap (MvPolynomial (Option τ) K)
      (MvPowerSeries (Option τ) K)) ((MvPolynomial.optionEquivLeft K τ).symm p))
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

 theorem algebraic_option_series_symm [IsDomain K]
    {f : PowerSeries (MvPowerSeries τ K)}
    (hf : IsAlgebraic (Polynomial (MvPolynomial τ K)) f) :
    IsAlgebraic (MvPolynomial (Option τ) K) ((MvPowerSeries.optionEquivLeft τ K).symm f) := by
  exact hf.ringHom_of_comp_eq (MvPolynomial.optionEquivLeft K τ).symm.toRingHom
    (MvPowerSeries.optionEquivLeft τ K).symm.toRingHom
    (MvPolynomial.optionEquivLeft K τ).symm.injective option_series_polynomial_square_symm.symm

 theorem algebraic_option_series [IsDomain K]
    {f : MvPowerSeries (Option τ) K}
    (hf : IsAlgebraic (MvPolynomial (Option τ) K) f) :
    IsAlgebraic (Polynomial (MvPolynomial τ K)) (MvPowerSeries.optionEquivLeft τ K f) := by
  exact hf.ringHom_of_comp_eq (MvPolynomial.optionEquivLeft K τ).toRingHom
    (MvPowerSeries.optionEquivLeft τ K).toRingHom
    (MvPolynomial.optionEquivLeft K τ).injective option_series_polynomial_square.symm

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial PowerSeries MvPolynomial
variable {A σ κ : Type*} [CommRing A] [IsDomain A]

 

theorem finite_weierstrass_unit_constraints
    (I : Ideal A) [IsAdicComplete I A]
    (h : Polynomial A) (hh : h.IsDistinguishedAt I)
    (hjac : (h : PowerSeries A)∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)))
    (a : σ → PowerSeries A) (f : κ → MvPolynomial σ (Polynomial A))
    (hf : ∀ k,eval₂ Polynomial.coeToPowerSeries.ringHom a (f k)=0)
    (D : MvPolynomial σ (Polynomial A)) (u : PowerSeries A)
    (hu : IsUnit u) (hD : eval₂ Polynomial.coeToPowerSeries.ringHom a D=(h : PowerSeries A)*u) :
    ∃ (r : σ → Polynomial A) (q : σ → PowerSeries A)
      (k : κ → Polynomial A) (w : Polynomial A),
      (∀ i,a i=(r i : PowerSeries A)+(h : PowerSeries A)^2*q i) ∧
      (∀ j,eval r (f j)=h^2*k j) ∧ eval r D=h*w ∧ IsUnit (w : PowerSeries A) := by
  obtain ⟨r,hrdeg,hr,hfrem,hDrem⟩ := finite_weierstrass_constraints I h hh a f hf D ⟨u,hD⟩
  have hr' (i : σ) : (h : PowerSeries A)^2∣a i-(r i : PowerSeries A) := by
    simpa only [pow_two,Polynomial.coe_mul] using hr i
  choose q hq using hr'
  have hfrem' (j : κ) : h^2∣eval r (f j) := by simpa only [pow_two] using hfrem j
  choose k hk using hfrem'
  obtain ⟨w,hw⟩ := hDrem
  refine ⟨r,q,k,w,fun i=>?_,hk,hw,?_⟩
  · linear_combination hq i
  · have hcon := eval₂_dvd_sub ((h*h : Polynomial A) : PowerSeries A) D a
      (fun i=>(r i : PowerSeries A)) hr
    have hmap := MvPolynomial.map_eval Polynomial.coeToPowerSeries.ringHom r D
    rw [MvPolynomial.eval_map] at hmap
    change ((eval r D : Polynomial A) : PowerSeries A) =
      eval₂ Polynomial.coeToPowerSeries.ringHom (fun i=>(r i : PowerSeries A)) D at hmap
    rw [←hmap,hD,hw,Polynomial.coe_mul] at hcon
    obtain ⟨z,hz⟩ := hcon
    simp only [Polynomial.coe_mul] at hz
    have hn : (h : PowerSeries A)≠0 := by exact_mod_cast hh.monic.ne_zero
    have he : u-(w : PowerSeries A)=(h : PowerSeries A)*z := by
      apply mul_left_cancel₀ hn
      rw [mul_sub]
      linear_combination hz
    have hw' : (w : PowerSeries A)=u+(-(h : PowerSeries A)*z) := by linear_combination -he
    rw [hw']
    have hneg : -(h : PowerSeries A)∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)) :=
      (Ideal.jacobson (⊥ : Ideal (PowerSeries A))).neg_mem hjac
    exact unit_add_jacobson hu ((Ideal.jacobson (⊥ : Ideal (PowerSeries A))).mul_mem_right _ hneg)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K τ : Type*} [Field K] [Finite τ]

 theorem jetIdeal_eq_maximalIdeal :
    jetIdeal (K:=K) (σ:=τ)=IsLocalRing.maximalIdeal (MvPowerSeries τ K) := by
  ext f
  rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero,not_not]
  rw [←pow_one (jetIdeal (K:=K) (σ:=τ)),mem_jetIdeal_pow_iff_coeff]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hz : Finsupp.degree d=0 := by omega
    have hd0 : d=0 := (Finsupp.degree_eq_zero_iff d).mp hz
    simpa only [hd0,MvPowerSeries.coeff_zero_eq_constantCoeff] using h

 theorem jetIdeal_pow_le_jacobson (n : ℕ) (hn : 0<n) :
    (jetIdeal (K:=K) (σ:=τ))^n≤Ideal.jacobson (⊥ : Ideal (MvPowerSeries τ K)) := by
  apply le_trans (Ideal.pow_le_self hn.ne')
  rw [jetIdeal_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal_le_jacobson _

omit [Finite τ] in
 theorem option_coefficient_jet_map_le :
    (jetIdeal (K:=K) (σ:=τ)).map
      ((MvPowerSeries.optionEquivLeft τ K).symm.toRingHom.comp PowerSeries.C)≤
        jetIdeal (K:=K) (σ:=Option τ) := by
  rw [jetIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  change (MvPowerSeries.optionEquivLeft τ K).symm (PowerSeries.C (MvPowerSeries.X i))∈_
  rw [←MvPowerSeries.optionEquivLeft_X_some,AlgEquiv.symm_apply_apply]
  exact Ideal.subset_span (Set.mem_range_self (some i))

omit [Finite τ] in
 theorem option_coefficient_jet_pow_map_le (n : ℕ) :
    ((jetIdeal (K:=K) (σ:=τ))^n).map
      ((MvPowerSeries.optionEquivLeft τ K).symm.toRingHom.comp PowerSeries.C)≤
        (jetIdeal (K:=K) (σ:=Option τ))^n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' option_coefficient_jet_map_le n

omit [Finite τ] in
 theorem option_inverse_coefficient_jet {n : ℕ} {f : PowerSeries (MvPowerSeries τ K)}
    (hf : f∈((jetIdeal (K:=K) (σ:=τ))^n).map PowerSeries.C) :
    (MvPowerSeries.optionEquivLeft τ K).symm f∈(jetIdeal (K:=K) (σ:=Option τ))^n := by
  have hm := Ideal.mem_map_of_mem (MvPowerSeries.optionEquivLeft τ K).symm.toRingHom hf
  rw [Ideal.map_map] at hm
  exact option_coefficient_jet_pow_map_le n hm

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial

 

def PolynomialArtinAt (K τ : Type*) [Field K] [Finite τ] : Prop :=
  ∀ (m r : ℕ) (f : Fin r → MvPolynomial (Fin m) (MvPolynomial τ K))
    (a : Fin m → MvPowerSeries τ K),
    (∀ k,MvPolynomial.aeval a (f k)=0) → ∀ n : ℕ,
    ∃ b : Fin m → MvPowerSeries τ K,
      (∀ k,MvPolynomial.aeval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n

 
theorem PolynomialArtinAt.finite {K τ σ κ : Type*} [Field K] [Finite τ]
    [Fintype σ] [Fintype κ] (h : PolynomialArtinAt K τ)
    (f : κ → MvPolynomial σ (MvPolynomial τ K)) (a : σ → MvPowerSeries τ K)
    (ha : ∀ k,MvPolynomial.aeval a (f k)=0) (n : ℕ) :
    ∃ b : σ → MvPowerSeries τ K,(∀ k,MvPolynomial.aeval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  classical
  let e := Fintype.equivFin σ
  let d := Fintype.equivFin κ
  let f' := fun k=>rename e (f (d.symm k))
  let a' := fun i=>a (e.symm i)
  have hr (v : σ → MvPowerSeries τ K) (p : MvPolynomial σ (MvPolynomial τ K)) :
      MvPolynomial.aeval (fun i=>v (e.symm i)) (rename e p)=MvPolynomial.aeval v p := by
    rw [MvPolynomial.aeval_def,eval₂_rename]
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    rfl
  have hf' (k : Fin (Fintype.card κ)) : MvPolynomial.aeval a' (f' k)=0 := by
    change MvPolynomial.aeval (fun i=>a (e.symm i)) (rename e (f (d.symm k)))=0
    rw [hr,ha]
  obtain ⟨b,hb,halg,hclose⟩ := h _ _ f' a' hf' n
  refine ⟨fun i=>b (e i),?_,fun i=>halg (e i),?_⟩
  · intro k
    have hv : (fun i=>b (e (e.symm i)))=b := by funext i; simp
    have he := hr (fun i=>b (e i)) (f k)
    rw [hv] at he
    rw [←he]
    have hd : f' (d k)=rename e (f k) := by simp [f']
    rw [←hd]
    exact hb (d k)
  · intro i
    simpa only [a',Equiv.symm_apply_apply] using hclose (e i)

end
end PD4Tensor.Spreading
end

end OAI
