import Mathlib
import OAI.Algebra.FiniteTensor.ArtinSteps

namespace OAI

/-! Jet stability of algebraic branches, coordinate removal and constant coefficients. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial MvPowerSeries

 

theorem polynomial_root_equal_of_jet {K τ : Type*} [CommRing K] [IsDomain K] [Finite τ]
    (P : Polynomial (MvPowerSeries τ K)) (a b : MvPowerSeries τ K)
    (ha : P.eval a=0) (hb : P.eval b=0) (hd : P.derivative.eval a≠0)
    (hclose : b-a∈(jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval a).order.toNat+1)) : b=a := by
  by_contra hne
  obtain ⟨q,hq⟩ := P.exists_mul_sq_add_linear_part_eq_eval_add a (b-a)
  rw [add_sub_cancel,ha,hb,add_zero] at hq
  have he : (b-a)*(P.derivative.eval a+(b-a)*q)=0 := by linear_combination hq
  have he' := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  have hmem : P.derivative.eval a∈(jetIdeal (K:=K) (σ:=τ))^
      ((P.derivative.eval a).order.toNat+1) := by
    have hz := ((jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval a).order.toNat+1)).neg_mem
      (((jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval a).order.toNat+1)).mul_mem_right q hclose)
    convert hz using 1
    linear_combination he'
  have ho := (mem_jetIdeal_pow_iff_order _ _).mp hmem
  rw [←ne_zero_iff_order_finite.mp hd] at ho
  exact Nat.not_succ_le_self _ (by exact_mod_cast ho)

 
theorem polynomial_eval₂_congr_ideal {B R : Type*} [CommRing B] [CommRing R]
    (I : Ideal R) (φ ψ : B →+* R) (a b : R)
    (hc : ∀ c,φ c-ψ c∈I) (hab : a-b∈I) (P : Polynomial B) :
    P.eval₂ φ a-P.eval₂ ψ b∈I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,sub_eq_zero]
  have hf : (Ideal.Quotient.mk I).comp φ=(Ideal.Quotient.mk I).comp ψ := by
    ext c
    exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (hc c)))
  have ha : Ideal.Quotient.mk I a=Ideal.Quotient.mk I b :=
    sub_eq_zero.mp ((map_sub _ _ _).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hab))
  rw [Polynomial.hom_eval₂,Polynomial.hom_eval₂,hf,ha]

 

theorem polynomial_moving_branch {B K τ : Type*} [CommRing B]
    [CommRing K] [IsDomain K] [Finite τ]
    (P : Polynomial B) (φ ψ : B →+* MvPowerSeries τ K)
    (a₀ a b : MvPowerSeries τ K)
    (hd : P.derivative.eval₂ ψ a₀≠0)
    (hc : ∀ c,φ c-ψ c∈(jetIdeal (K:=K) (σ:=τ))^
      ((P.derivative.eval₂ ψ a₀).order.toNat+1))
    (ha : a-a₀∈(jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval₂ ψ a₀).order.toNat+1))
    (hb : b-a₀∈(jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval₂ ψ a₀).order.toNat+1))
    (hea : P.eval₂ φ a=0) (heb : P.eval₂ φ b=0) : b=a := by
  have hdc := polynomial_eval₂_congr_ideal _ φ ψ a a₀ hc ha P.derivative
  have hdn := ne_zero_of_close_jet hd hdc
  have hdo := order_eq_of_close_jet hd hdc
  apply polynomial_root_equal_of_jet (P.map φ) a b
  · simpa only [eval_map] using hea
  · simpa only [eval_map] using heb
  · simpa only [derivative_map,eval_map] using hdn
  · simp only [derivative_map,eval_map,hdo]
    convert ((jetIdeal (K:=K) (σ:=τ))^((P.derivative.eval₂ ψ a₀).order.toNat+1)).sub_mem hb ha using 1
    abel

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ : Type*} [CommRing K] [Finite σ] [Finite τ]

 theorem truncTotal_eq_of_close (a b : MvPowerSeries τ K) (n : ℕ)
    (h : a-b∈(jetIdeal (K:=K) (σ:=τ))^n) : truncTotal n a=truncTotal n b := by
  ext d
  by_cases hd : d.degree<n
  · rw [coeff_truncTotal _ hd,coeff_truncTotal _ hd]
    have he := (mem_jetIdeal_pow_iff_coeff _ _).mp h d hd
    simpa only [map_sub,sub_eq_zero] using he
  · simp [coeff_truncTotal_eq_zero _ (Nat.le_of_not_gt hd)]

 theorem close_of_truncTotal_eq (a b : MvPowerSeries τ K) (n : ℕ)
    (h : truncTotal n a=truncTotal n b) : a-b∈(jetIdeal (K:=K) (σ:=τ))^n := by
  apply (mem_jetIdeal_pow_iff_coeff _ _).mpr
  intro d hd
  have he := congrArg (fun polynomial => polynomial.coeff d) h
  rw [coeff_truncTotal _ hd,coeff_truncTotal _ hd] at he
  simpa only [map_sub,sub_eq_zero] using he

 

theorem subst_close_jet (f : MvPowerSeries σ K) (a b : σ → MvPowerSeries τ K)
    (ha : ∀ i,constantCoeff (a i)=0) (hb : ∀ i,constantCoeff (b i)=0) (n : ℕ)
    (h : ∀ i,a i-b i∈(jetIdeal (K:=K) (σ:=τ))^n) :
    subst a f-subst b f∈(jetIdeal (K:=K) (σ:=τ))^n := by
  apply close_of_truncTotal_eq
  have hc : (fun i=>((a i).truncTotal n : MvPowerSeries τ K))=
      fun i=>((b i).truncTotal n : MvPowerSeries τ K) := by
    funext i
    rw [truncTotal_eq_of_close (a i) (b i) n (h i)]
  rw [truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero ha) (x:=fun _=>n) (fun _=>le_rfl),
    truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero hb) (x:=fun _=>n) (fun _=>le_rfl),hc]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ : Type*} [CommRing K] [IsDomain K] [Finite σ] [Finite τ]

 
omit [IsDomain K] [Finite τ] in
theorem aeval_relation_subst (F : MvPowerSeries σ K)
    (P : Polynomial (MvPolynomial σ K))
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,constantCoeff (a i)=0) :
    P.eval₂ (MvPolynomial.aeval a).toRingHom (subst a F)=
      subst a (Polynomial.aeval F P) := by
  let A := substAlgHom (R:=K) (hasSubst_of_constantCoeff_zero ha)
  have he : A.toRingHom.comp (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K))=
      (MvPolynomial.aeval a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [A,MvPowerSeries.algebraMap_apply',MvPowerSeries.algebraMap_apply]
    · intro i
      simp [A,MvPowerSeries.algebraMap_apply',
        subst_X (hasSubst_of_constantCoeff_zero ha)]
  rw [←substAlgHom_apply (hasSubst_of_constantCoeff_zero ha),
    ←substAlgHom_apply (hasSubst_of_constantCoeff_zero ha)]
  change P.eval₂ (MvPolynomial.aeval a).toRingHom (A F)=A (Polynomial.aeval F P)
  rw [Polynomial.aeval_def]
  change P.eval₂ (MvPolynomial.aeval a).toRingHom (A F)=A.toRingHom (P.eval₂ _ F)
  rw [Polynomial.hom_eval₂,he]
  rfl

 

theorem germ_branch_stability (F : MvPowerSeries σ K)
    (P : Polynomial (MvPolynomial σ K)) (hP : Polynomial.aeval F P=0)
    (a₀ a : σ → MvPowerSeries τ K)
    (h₀ : ∀ i,constantCoeff (a₀ i)=0) (ha : ∀ i,constantCoeff (a i)=0)
    (hd : subst a₀ (Polynomial.aeval F P.derivative)≠0)
    (hc : ∀ i,a i-a₀ i∈(jetIdeal (K:=K) (σ:=τ))^
      ((subst a₀ (Polynomial.aeval F P.derivative)).order.toNat+1))
    (b : MvPowerSeries τ K)
    (hb : b-subst a₀ F∈(jetIdeal (K:=K) (σ:=τ))^
      ((subst a₀ (Polynomial.aeval F P.derivative)).order.toNat+1))
    (hroot : P.eval₂ (MvPolynomial.aeval a).toRingHom b=0) : b=subst a F := by
  have he := aeval_relation_subst F P.derivative a₀ h₀
  apply polynomial_moving_branch P (MvPolynomial.aeval a).toRingHom
    (MvPolynomial.aeval a₀).toRingHom (subst a₀ F) (subst a F) b
  · rwa [he]
  · intro c
    rw [he]
    change (MvPolynomial.aeval a) c-(MvPolynomial.aeval a₀) c∈_
    simpa only [subst_coe] using subst_close_jet (c : MvPowerSeries σ K) a a₀ ha h₀ _ hc
  · rw [he]
    exact subst_close_jet F a a₀ ha h₀ _ hc
  · rwa [he]
  · rw [aeval_relation_subst F P a ha,hP,←substAlgHom_apply (hasSubst_of_constantCoeff_zero ha),map_zero]
  · exact hroot

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial
variable {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A]

 
 

omit [IsDomain B] in
theorem algebraic_constantCoeff {f : PowerSeries A}
    (hf : IsAlgebraic (Polynomial B) f) :
    IsAlgebraic B (PowerSeries.constantCoeff f) := by
  obtain ⟨P,hP,hPf⟩ := hf
  let Q := Bivariate.swap P
  have hQ : Q≠0 := fun hz=>hP (Bivariate.swap.injective (by simpa only [map_zero] using hz))
  obtain ⟨n,q,hq,hq0⟩ := polynomial_remove_X_factor Q hQ
  let E : Polynomial (Polynomial B) →+* PowerSeries A :=
    eval₂RingHom (aeval f).toRingHom PowerSeries.X
  have hmap : (aeval (PowerSeries.X : PowerSeries A) : Polynomial B →ₐ[B] PowerSeries A).toRingHom =
      algebraMap (Polynomial B) (PowerSeries A) := by
    apply Polynomial.ringHom_ext
    · intro b
      simp [PowerSeries.algebraMap_apply',PowerSeries.algebraMap_apply]
    · simp [PowerSeries.algebraMap_apply']
  have heswap : E.comp Bivariate.swap.toRingHom =
      (aeval f : Polynomial (Polynomial B) →ₐ[Polynomial B] PowerSeries A).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro p
      change E (Bivariate.swap (C p))=(aeval f) (C p)
      rw [Bivariate.swap_C,aeval_C]
      change eval₂ (aeval f).toRingHom PowerSeries.X (p.map C)=_
      rw [eval₂_map]
      have hc : (aeval f).toRingHom.comp (C : B →+* Polynomial B)=algebraMap B (PowerSeries A) := by
        ext b
        simp
      rw [hc]
      exact RingHom.congr_fun hmap p
    · simp [E,Bivariate.swap_Y]
  have hE : E Q=0 := by
    exact (RingHom.congr_fun heswap P).trans hPf
  have hqeval : E q=0 := by
    rw [hq,map_mul,map_pow] at hE
    have hx : E X=PowerSeries.X := by simp [E]
    rw [hx] at hE
    exact (mul_eq_zero.mp hE).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  refine ⟨q.coeff 0,hq0,?_⟩
  have he := congrArg PowerSeries.constantCoeff hqeval
  have hhom : PowerSeries.constantCoeff.comp E =
      ((aeval (PowerSeries.constantCoeff f)).toRingHom).comp (evalRingHom (0 : Polynomial B)) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.comp_apply,E,coe_eval₂RingHom,eval₂_C,coe_evalRingHom,eval_C]
      change PowerSeries.constantCoeff (aeval f p)=aeval (PowerSeries.constantCoeff f) p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp,hq]
      | monomial n b => simp [aeval_monomial,PowerSeries.algebraMap_apply]
    · simp [E]
  have hc := RingHom.congr_fun hhom q
  have hz := hc.symm.trans he
  simp only [RingHom.comp_apply,coe_evalRingHom,←coeff_zero_eq_eval_zero,map_zero] at hz
  exact hz

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K σ : Type*} [CommRing K] [IsDomain K] [Finite σ]

omit [IsDomain K] [Finite σ] in
 theorem algebraic_optionEquiv {f : MvPowerSeries (Option σ) K}
    (hf : IsAlgebraic (MvPolynomial (Option σ) K) f) :
    IsAlgebraic (Polynomial (MvPolynomial σ K)) (MvPowerSeries.optionEquivLeft σ K f) := by
  apply hf.ringHom_of_comp_eq (MvPolynomial.optionEquivLeft K σ).toRingHom
    (MvPowerSeries.optionEquivLeft σ K).toRingHom (MvPolynomial.optionEquivLeft K σ).injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [MvPolynomial.optionEquivLeft_C,MvPowerSeries.algebraMap_apply',
      PowerSeries.algebraMap_apply']
  · intro i
    cases i <;> simp [MvPowerSeries.algebraMap_apply',PowerSeries.algebraMap_apply']

 

omit [Finite σ] in
 theorem algebraic_drop_option {f : MvPowerSeries (Option σ) K}
    (hf : IsAlgebraic (MvPolynomial (Option σ) K) f) :
    IsAlgebraic (MvPolynomial σ K)
      (PowerSeries.constantCoeff (MvPowerSeries.optionEquivLeft σ K f)) := by
  let : IsDomain (MvPowerSeries σ K) := NoZeroDivisors.to_isDomain _
  exact algebraic_constantCoeff (algebraic_optionEquiv hf)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ υ : Type*} [CommRing K] [IsDomain K]

omit [IsDomain K] in
 theorem algebraic_rename_equiv (e : σ ≃ τ) {f : MvPowerSeries σ K}
    (hf : IsAlgebraic (MvPolynomial σ K) f) :
    IsAlgebraic (MvPolynomial τ K) (rename e f) := by
  apply hf.ringHom_of_comp_eq (MvPolynomial.rename e).toRingHom
    (rename e).toRingHom (MvPolynomial.rename_injective _ e.injective)
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [MvPowerSeries.algebraMap_apply']
  · intro i
    simp [MvPowerSeries.algebraMap_apply']

omit [IsDomain K] in
 theorem killCompl_comp_apply (e : σ ↪ τ) (g : τ ↪ υ) (f : MvPowerSeries υ K) :
    killCompl e (killCompl g f)=killCompl (e.trans g) f := by
  ext d
  simp only [coeff_killCompl,Finsupp.embDomain_trans_apply]

omit [IsDomain K] in
 theorem killCompl_equiv (e : σ ≃ τ) (f : MvPowerSeries τ K) :
    killCompl e.toEmbedding f=rename e.symm f := by
  have h := killCompl_rename_app (e:=e.toEmbedding) (rename e.symm f)
  have he : rename e.toEmbedding (rename e.symm f)=f :=
    (renameEquiv K e).apply_symm_apply f
  rwa [he] at h

omit [IsDomain K] in
 theorem drop_ne_eq_killCompl [DecidableEq τ] (t : τ) (f : MvPowerSeries τ K) :
    PowerSeries.constantCoeff (optionEquivLeft {i : τ // i≠t} K
      (rename (Equiv.optionSubtypeNe t).symm f))=
      killCompl (Function.Embedding.subtype (fun i : τ=>i≠t)) f := by
  classical
  ext d
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_coeff_optionEquivLeft,coeff_killCompl]
  let E := Equiv.optionSubtypeNe t
  let j : {i : τ // i≠t} ↪ τ := Function.Embedding.subtype _
  have hh : j.trans E.symm.toEmbedding=Function.Embedding.some := by
    apply Function.Embedding.ext
    intro i
    exact Equiv.optionSubtypeNe_symm_of_ne i.property
  have hd : Finsupp.embDomain E.symm.toEmbedding (Finsupp.embDomain j d)=d.optionElim 0 := by
    rw [←Finsupp.embDomain_trans_apply,hh]
    ext i
    cases i <;> simp
  rw [←hd]
  exact coeff_embDomain_rename E.symm.toEmbedding f _

 theorem algebraic_drop_ne [Finite τ] (t : τ) {f : MvPowerSeries τ K}
    (hf : IsAlgebraic (MvPolynomial τ K) f) :
    IsAlgebraic (MvPolynomial {i : τ // i≠t} K)
      (killCompl (Function.Embedding.subtype (fun i : τ=>i≠t)) f) := by
  classical
  rw [←drop_ne_eq_killCompl]
  exact algebraic_drop_option (algebraic_rename_equiv (Equiv.optionSubtypeNe t).symm hf)

 

 theorem algebraic_killCompl [Finite σ] [Finite τ] (e : σ ↪ τ) {f : MvPowerSeries τ K}
    (hf : IsAlgebraic (MvPolynomial τ K) f) :
    IsAlgebraic (MvPolynomial σ K) (killCompl e f) := by
  classical
  generalize hn : Nat.card τ=n
  induction n using Nat.strong_induction_on generalizing τ with
  | h n ih =>
    by_cases he : Function.Surjective e
    · let E : σ ≃ τ := Equiv.ofBijective e ⟨e.injective,he⟩
      have hh : e=E.toEmbedding := by ext i; rfl
      rw [hh,killCompl_equiv]
      exact algebraic_rename_equiv E.symm hf
    · simp only [Function.Surjective, not_forall, not_exists] at he
      obtain ⟨t,ht⟩ := he
      let j : {i : τ // i≠t} ↪ τ := Function.Embedding.subtype _
      let e' : σ ↪ {i : τ // i≠t} :=
        ⟨fun i=>⟨e i,ht i⟩,fun _ _ h=>e.injective (congrArg Subtype.val h)⟩
      have hcomp : e'.trans j=e := by ext i; rfl
      have hlt : Nat.card {i : τ // i≠t}<n := by
        rw [←hn]
        let := Fintype.ofFinite τ
        simpa only [Nat.card_eq_fintype_card] using
          (Fintype.card_subtype_lt (p:=fun i : τ=>i≠t) (x:=t) (not_not.mpr rfl))
      have h := ih (Nat.card {i : τ // i≠t}) hlt e' (algebraic_drop_ne t hf) rfl
      rwa [killCompl_comp_apply,hcomp] at h

end
end PD4Tensor.Spreading
end

end OAI
