import Mathlib
import OAI.Algebra.FiniteTensor.JetSystems
import OAI.Algebra.FiniteTensor.PositiveObstruction

namespace OAI

/-! Parameter-series equivalences, nilpotent root lifting and algebraic descent. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable (A : Type*) [CommRing A] (m : ℕ) (σ : Type*)

 

def parametersToSeries : Parameters (MvPowerSeries σ A) m →+*
    MvPowerSeries σ (Parameters A m) :=
  Ideal.Quotient.lift (squareIdeal (MvPowerSeries σ A) m)
    (MvPolynomial.eval₂Hom (MvPowerSeries.map (algebraMap A (Parameters A m)))
      (fun i=>MvPowerSeries.C (parameter A m i))) (by
    have h : squareIdeal (MvPowerSeries σ A) m≤RingHom.ker
        (MvPolynomial.eval₂Hom (MvPowerSeries.map (algebraMap A (Parameters A m)))
          (fun i=>MvPowerSeries.C (parameter A m i))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (MvPolynomial.eval₂Hom _ _) (MvPolynomial.X i ^ 2) = 0
      rw [map_pow,MvPolynomial.eval₂Hom_X',←map_pow,parameter_sq,map_zero]
    exact fun a ha=>h ha)

@[simp] theorem parametersToSeries_algebraMap (f : MvPowerSeries σ A) :
    parametersToSeries A m σ (algebraMap (MvPowerSeries σ A) (Parameters (MvPowerSeries σ A) m) f)=
      MvPowerSeries.map (algebraMap A (Parameters A m)) f := by
  change (MvPolynomial.eval₂Hom _ _) (MvPolynomial.C f)=_
  exact MvPolynomial.eval₂Hom_C _ _ _

@[simp] theorem parametersToSeries_parameter (i : Fin m) :
    parametersToSeries A m σ (parameter (MvPowerSeries σ A) m i)=
      MvPowerSeries.C (parameter A m i) := by
  change (MvPolynomial.eval₂Hom _ _) (MvPolynomial.X i)=_
  exact MvPolynomial.eval₂Hom_X' _ _ _

 theorem parametersToSeries_boxMonomial (q : Box m) :
    parametersToSeries A m σ (boxMonomial (MvPowerSeries σ A) m q)=
      MvPowerSeries.C (boxMonomial A m q) := by
  change (MvPolynomial.eval₂Hom _ _) (MvPolynomial.monomial (boxExponent m q) 1)=_
  rw [MvPolynomial.eval₂Hom_monomial,map_one,one_mul]
  unfold boxMonomial
  rw [MvPolynomial.monomial_eq]
  simp only [map_one,one_mul,Finsupp.prod,map_prod,map_pow,parameter]

 theorem parametersToSeries_eq_assemble (f : Parameters (MvPowerSeries σ A) m) :
    parametersToSeries A m σ f=assembleBox (fun q=>boxCoeff (MvPowerSeries σ A) m q f) := by
  conv_lhs => rw [←sum_boxMonomial (MvPowerSeries σ A) m f]
  rw [map_sum]
  unfold assembleBox
  apply Finset.sum_congr rfl
  intro q _
  rw [Algebra.smul_def (R:=MvPowerSeries σ A) (A:=Parameters (MvPowerSeries σ A) m),map_mul,parametersToSeries_algebraMap,parametersToSeries_boxMonomial]
  exact mul_comm _ _

@[simp] theorem boxSeries_parametersToSeries (f : Parameters (MvPowerSeries σ A) m) (q : Box m) :
    boxSeries A m q (parametersToSeries A m σ f)=boxCoeff (MvPowerSeries σ A) m q f := by
  rw [parametersToSeries_eq_assemble,boxSeries_assembleBox]

 theorem parametersToSeries_bijective : Function.Bijective (parametersToSeries A m σ) := by
  constructor
  · intro f g h
    apply parameters_ext (MvPowerSeries σ A) m
    intro q
    rw [←boxSeries_parametersToSeries,←boxSeries_parametersToSeries,h]
  · intro f
    refine ⟨∑ q:Box m,boxSeries A m q f • boxMonomial (MvPowerSeries σ A) m q,?_⟩
    calc
      _ = ∑ q:Box m,MvPowerSeries.C (boxMonomial A m q)*
          MvPowerSeries.map (algebraMap A (Parameters A m)) (boxSeries A m q f) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [Algebra.smul_def (R:=MvPowerSeries σ A) (A:=Parameters (MvPowerSeries σ A) m),map_mul,parametersToSeries_algebraMap,parametersToSeries_boxMonomial]
        exact mul_comm _ _
      _ = f := sum_boxSeries A m f

def seriesParameterEquiv : MvPowerSeries σ (Parameters A m) ≃+* Parameters (MvPowerSeries σ A) m :=
  (RingEquiv.ofBijective (parametersToSeries A m σ) (parametersToSeries_bijective A m σ)).symm

 theorem boxCoeff_seriesParameterEquiv (f : MvPowerSeries σ (Parameters A m)) (q : Box m) :
    boxCoeff (MvPowerSeries σ A) m q (seriesParameterEquiv A m σ f)=boxSeries A m q f := by
  rw [←boxSeries_parametersToSeries]
  change boxSeries A m q ((seriesParameterEquiv A m σ).symm (seriesParameterEquiv A m σ f))=_
  rw [RingEquiv.symm_apply_apply]

@[simp] theorem seriesParameterEquiv_map (f : MvPowerSeries σ A) :
    seriesParameterEquiv A m σ (MvPowerSeries.map (algebraMap A (Parameters A m)) f)=
      algebraMap (MvPowerSeries σ A) (Parameters (MvPowerSeries σ A) m) f := by
  apply (seriesParameterEquiv A m σ).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (parametersToSeries_algebraMap A m σ f).symm

 theorem augmentation_eq_boxCoeff_zero (x : Parameters A m) :
    augmentation A m x=boxCoeff A m (fun _=>0) x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change MvPolynomial.eval₂Hom (RingHom.id A) (fun _=>0) p=p.coeff _
  have hz : boxExponent m (fun _=>0)=0 := by ext i; simp
  rw [hz]
  exact MvPolynomial.eval₂Hom_zero_apply (RingHom.id A) p

 theorem augmentation_seriesParameterEquiv (f : MvPowerSeries σ (Parameters A m)) :
    augmentation (MvPowerSeries σ A) m (seriesParameterEquiv A m σ f)=
      MvPowerSeries.map (augmentation A m) f := by
  rw [augmentation_eq_boxCoeff_zero,boxCoeff_seriesParameterEquiv]
  ext d
  rw [coeff_boxSeries,MvPowerSeries.coeff_map,augmentation_eq_boxCoeff_zero]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial
open scoped Ring

 

theorem root_lift_nilpotent {R : Type*} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (f : Polynomial R) (a₀ : R) (h₀ : f.eval a₀∈I)
    (hd : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R,f.eval a=0 ∧ a-a₀∈I := by
  classical
  let f' := f.derivative
  let c : ℕ → R := fun n=>Nat.recOn n a₀ (fun _ b=>b-f.eval b*(f'.eval b)⁻¹ʳ)
  have hc (n : ℕ) : c (n+1)=c n-f.eval (c n)*(f'.eval (c n))⁻¹ʳ := rfl
  have hc_mod (n : ℕ) : c n≡a₀ [SMOD I] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc,sub_eq_add_neg,←add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero,Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [←SModEq.zero] at h₀ ⊢
      exact (ih.eval f).trans h₀
  have hd_c (n : ℕ) : IsUnit (f'.eval (c n)) := by
    apply hI.isUnit_quotient_mk_iff.mp
    have heq := SModEq.def.mp ((hc_mod n).eval f')
    change (Ideal.Quotient.mk I) (f'.eval (c n)) = (Ideal.Quotient.mk I) (f'.eval a₀) at heq
    rw [heq]
    exact hd.map (Ideal.Quotient.mk I)
  have hfc (n : ℕ) : f.eval (c n)∈I^(n+1) := by
    induction n with
    | zero => simpa only [c,Nat.rec_zero,zero_add,pow_one] using h₀
    | succ n ih =>
      rw [←taylor_eval_sub (c n),hc,sub_eq_add_neg,sub_eq_add_neg,add_neg_cancel_comm]
      rw [eval_eq_sum,sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [←one_add_one_eq_two,Finset.sum_range_succ,Finset.range_one,Finset.sum_singleton,
          taylor_coeff_zero,taylor_coeff_one,pow_zero,pow_one,mul_one,mul_neg,
          mul_left_comm,Ring.mul_inverse_cancel _ (hd_c n),mul_one,add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i,_⟩
        have hle : n + 2 ≤ i * (n + 1) := by nlinarith
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _ ih)) _
  obtain ⟨N,hN⟩ := hI
  refine ⟨c N,?_,?_⟩
  · have hm : f.eval (c N)∈I^N := Ideal.pow_le_pow_right (Nat.le_succ N) (hfc N)
    simpa only [hN,Ideal.zero_eq_bot,Ideal.mem_bot] using hm
  · exact SModEq.sub_mem.mp (hc_mod N)

 

theorem root_unique_nilpotent {R : Type*} [CommRing R]
    (f : Polynomial R) (a b : R) (ha : f.eval a=0) (hb : f.eval b=0)
    (hnil : IsNilpotent (b-a)) (hd : IsUnit (f.derivative.eval a)) : a=b := by
  obtain ⟨c,hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add f a (b-a)
  have hz : (c*(b-a)+f.derivative.eval a)*(b-a)=0 := by
    rw [show a+(b-a)=b by abel] at hc
    rw [ha,hb] at hc
    linear_combination hc
  have hu : IsUnit (c*(b-a)+f.derivative.eval a) :=
    (show IsNilpotent (c*(b-a)) from by
      obtain ⟨N,hN⟩ := hnil
      exact ⟨N,by rw [mul_pow,hN,mul_zero]⟩).isUnit_add_right_of_commute hd (Commute.all _ _)
  have hzero : b-a=0 := (hu.mul_right_eq_zero).mp hz
  exact (sub_eq_zero.mp hzero).symm

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable (A : Type*) [CommRing A] (m : ℕ)

 theorem parameterIdeal_nilpotent : IsNilpotent (parameterIdeal A m) := by
  apply (Ideal.FG.isNilpotent_iff_le_nilradical ?_).mpr (parameterIdeal_le_nilradical A m)
  exact Submodule.fg_span (Set.finite_range (parameter A m))

 theorem parameter_sub_constant_mem (x : Parameters A m) :
    x-algebraMap A (Parameters A m) (augmentation A m x)∈parameterIdeal A m := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
      change algebraMap A (Parameters A m) a-algebraMap A (Parameters A m)
        (augmentation A m (algebraMap A (Parameters A m) a))∈parameterIdeal A m
      simp
  | add p q hp hq =>
      simpa only [map_add,add_sub_add_comm] using (parameterIdeal A m).add_mem hp hq
  | mul_X p i _ =>
      simp only [map_mul,show Ideal.Quotient.mk (squareIdeal A m) (MvPolynomial.X i)=
        parameter A m i from rfl,augmentation_parameter,mul_zero,map_zero,sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

 theorem parameter_mem_iff_augmentation_zero (x : Parameters A m) :
    x∈parameterIdeal A m ↔ augmentation A m x=0 := by
  constructor
  · intro hx
    have hle : parameterIdeal A m ≤ RingHom.ker (augmentation A m) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact augmentation_parameter A m i
    exact hle hx
  · intro hx
    simpa only [hx,map_zero,sub_zero] using parameter_sub_constant_mem A m x

 theorem parameter_isUnit_of_augmentation {K : Type*} [Field K] (x : Parameters K m)
    (hx : augmentation K m x≠0) : IsUnit x := by
  have hn : IsNilpotent (x-algebraMap K (Parameters K m) (augmentation K m x)) :=
    mem_nilradical.mp (parameterIdeal_le_nilradical K m (parameter_sub_constant_mem K m x))
  have hu := (isUnit_iff_ne_zero.mpr hx).map (algebraMap K (Parameters K m))
  simpa only [add_sub_cancel] using hn.isUnit_add_left_of_commute hu (Commute.all _ _)

 

theorem squarefree_root_descent {E : Type*} [Field E] (k : Subfield E)
    (P : Polynomial (Parameters k m)) (x : Parameters E m)
    (hx : (P.map (mapParameters k.subtype)).eval x=0)
    (hx₀ : augmentation E m x∈k)
    (hd : augmentation E m ((P.map (mapParameters k.subtype)).derivative.eval x)≠0) :
    ∃ y : Parameters k m,mapParameters k.subtype y=x := by
  let x₀ : k := ⟨augmentation E m x,hx₀⟩
  let a₀ : Parameters k m := algebraMap k (Parameters k m) x₀
  have comm (Q : Polynomial (Parameters k m)) (a : Parameters k m) :
      k.subtype (augmentation k m (Q.eval a))=
        augmentation E m ((Q.map (mapParameters k.subtype)).eval (mapParameters k.subtype a)) := by
    rw [Polynomial.eval_map_apply,augmentation_mapParameters]
  have haug (a : Parameters E m) (Q : Polynomial (Parameters E m)) :
      augmentation E m (Q.eval a)=
        (Q.map (augmentation E m)).eval (augmentation E m a) := by
    rw [Polynomial.eval_map,Polynomial.eval₂_at_apply]
  have ha₀ : augmentation E m (mapParameters k.subtype a₀)=augmentation E m x := by
    simp only [a₀,augmentation_mapParameters,augmentation_algebraMap,x₀,Subfield.subtype_apply]
  have hroot₀ : P.eval a₀∈parameterIdeal k m := by
    rw [parameter_mem_iff_augmentation_zero]
    apply k.subtype.injective
    rw [comm,haug,ha₀,←haug,hx,map_zero,map_zero]
  have hd₀ : IsUnit (P.derivative.eval a₀) := by
    apply parameter_isUnit_of_augmentation m
    intro hz
    apply hd
    rw [Polynomial.derivative_map, haug, ←ha₀, ←haug, ←comm, hz, map_zero]
  obtain ⟨y,hy,hy₀⟩ := root_lift_nilpotent (parameterIdeal k m)
    (parameterIdeal_nilpotent k m) P a₀ hroot₀ hd₀
  refine ⟨y,?_⟩
  have hy_map : (P.map (mapParameters k.subtype)).eval (mapParameters k.subtype y)=0 := by
    rw [Polynomial.eval_map,Polynomial.eval₂_at_apply,hy,map_zero]
  have hy_aug : augmentation E m (mapParameters k.subtype y)=augmentation E m x := by
    have h := (parameter_mem_iff_augmentation_zero k m _).mp hy₀
    simp only [map_sub,sub_eq_zero] at h
    rw [augmentation_mapParameters,h]
    simpa only [augmentation_mapParameters] using ha₀
  apply root_unique_nilpotent (P.map (mapParameters k.subtype)) _ _ hy_map hx
  · apply mem_nilradical.mp
    apply parameterIdeal_le_nilradical E m
    rw [parameter_mem_iff_augmentation_zero,map_sub,hy_aug,sub_self]
  · apply parameter_isUnit_of_augmentation m
    rw [haug,hy_aug,←haug]
    exact hd

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {R E : Type*} [CommRing R] [IsDomain R] [Field E] [Algebra R E]

 

def algebraicSubfield : Subfield E where
  carrier := {x | IsAlgebraic R x}
  zero_mem' := isAlgebraic_zero
  one_mem' := isAlgebraic_one
  add_mem' := IsAlgebraic.add
  mul_mem' := IsAlgebraic.mul
  neg_mem' := IsAlgebraic.neg
  inv_mem' := fun _ h=>h.inv

 theorem mem_algebraicSubfield (x : E) :
    x∈algebraicSubfield (R:=R) (E:=E) ↔ IsAlgebraic R x := Iff.rfl

variable (m : ℕ)

 theorem exists_parameter_lift (k : Subfield E) (x : Parameters E m)
    (hx : ∀ q,boxCoeff E m q x∈k) :
    ∃ y : Parameters k m,mapParameters k.subtype y=x := by
  classical
  refine ⟨∑ q:Box m,(⟨boxCoeff E m q x,hx q⟩ : k) • boxMonomial k m q,?_⟩
  apply parameters_ext E m
  intro b
  rw [boxCoeff_mapParameters]
  change k.subtype _=k.subtype ⟨boxCoeff E m b x,hx b⟩
  congr 1
  simp only [map_sum,map_smul,boxCoeff_boxMonomial,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp

 theorem mem_parameter_range (k : Subfield E) (x : Parameters E m) :
    x∈(mapParameters (m:=m) k.subtype).range ↔ ∀ q,boxCoeff E m q x∈k := by
  constructor
  · rintro ⟨y,rfl⟩ q
    rw [boxCoeff_mapParameters]
    exact (boxCoeff k m q y).property
  · exact exists_parameter_lift m k x

def parameterRangeEquiv (k : Subfield E) : Parameters k m ≃+*
    (mapParameters (m:=m) k.subtype).range :=
  RingEquiv.ofBijective (mapParameters (m:=m) k.subtype).rangeRestrict
    ⟨fun _ _ h=>mapParameters_injective k.subtype k.subtype.injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

 

def liftParametersHom {A : Type*} [CommRing A] (k : Subfield E)
    (f : A →+* Parameters E m) (hf : ∀ a,∀ q,boxCoeff E m q (f a)∈k) :
    A →+* Parameters k m :=
  (parameterRangeEquiv m k).symm.toRingHom.comp
      (f.codRestrict _ (fun a=>(mem_parameter_range m k (f a)).mpr (hf a)))

 theorem map_liftParametersHom {A : Type*} [CommRing A] (k : Subfield E)
    (f : A →+* Parameters E m) (hf : ∀ a,∀ q,boxCoeff E m q (f a)∈k) (a : A) :
    mapParameters k.subtype (liftParametersHom m k f hf a)=f a := by
  change (mapParameters k.subtype)
    ((parameterRangeEquiv m k).symm ⟨f a,_⟩)=f a
  exact congrArg Subtype.val ((parameterRangeEquiv m k).apply_symm_apply ⟨f a,_⟩)

 theorem squarefree_root_algebraic (P : Polynomial (Parameters E m)) (x : Parameters E m)
    (hP : ∀ n q,IsAlgebraic R (boxCoeff E m q (P.coeff n)))
    (hx : P.eval x=0) (hx₀ : IsAlgebraic R (augmentation E m x))
    (hd : augmentation E m (P.derivative.eval x)≠0) :
    ∀ q,IsAlgebraic R (boxCoeff E m q x) := by
  let k := algebraicSubfield (R:=R) (E:=E)
  have hp (n : ℕ) : ∃ y : Parameters k m,mapParameters k.subtype y=P.coeff n :=
    exists_parameter_lift m k (P.coeff n) (hP n)
  let Q : Polynomial (Parameters k m) :=
    ∑ n∈P.support,Polynomial.monomial n (hp n).choose
  have hQ : Q.map (mapParameters k.subtype)=P := by
    unfold Q
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_monomial,(hp _).choose_spec]
    exact Polynomial.sum_monomial_eq P
  obtain ⟨y,hy⟩ := squarefree_root_descent m k Q x (hQ.symm ▸ hx) hx₀ (hQ.symm ▸ hd)
  intro q
  rw [←hy,boxCoeff_mapParameters]
  exact (boxCoeff k m q y).property

end
end PD4Tensor.Spreading
end

end OAI
