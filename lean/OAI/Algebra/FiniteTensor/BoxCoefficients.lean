import Mathlib
import OAI.Algebra.FiniteTensor.ScalarModels

namespace OAI

/-! Squarefree box coefficients and finite tensor primitives. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
open scoped BigOperators
variable (A : Type*) [CommRing A] (m : ℕ)

abbrev Box := Fin m → Fin 2

def boxExponent (b : Box m) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (b i).val)

@[simp] theorem boxExponent_apply (b : Box m) (i : Fin m) : boxExponent m b i=(b i).val := by
  simp [boxExponent]

 theorem boxExponent_injective : Function.Injective (boxExponent m) := by
  intro b c h
  funext i
  apply Fin.ext
  simpa only [boxExponent_apply] using congrArg (fun f : Fin m →₀ ℕ => f i) h

 theorem squareIdeal_as_monomials : squareIdeal A m =
    Ideal.span ((fun a : Fin m →₀ ℕ => MvPolynomial.monomial a (1 : A)) ''
      Set.range (fun i : Fin m => Finsupp.single i 2)) := by
  unfold squareIdeal
  congr 1
  ext f
  simp only [Set.mem_range,Set.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨Finsupp.single i 2,⟨i,rfl⟩,MvPolynomial.X_pow_eq_monomial.symm⟩
  · rintro ⟨a,⟨i,rfl⟩,rfl⟩
    exact ⟨i,MvPolynomial.X_pow_eq_monomial⟩

 theorem squareIdeal_coeff_iff (f : MvPolynomial (Fin m) A) :
    f∈squareIdeal A m ↔ ∀ b : Box m,f.coeff (boxExponent m b)=0 := by
  classical
  rw [squareIdeal_as_monomials,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro hf b
    by_contra hb
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := hf _ (MvPolynomial.mem_support_iff.mpr hb)
    have hpi : 2≤(b i).val := by simpa only [Finsupp.single_eq_same,boxExponent_apply] using hi i
    exact (not_le_of_gt (b i).isLt) hpi
  · intro hf a ha
    have hn : ¬∀ i,a i<2 := by
      intro h
      let b : Box m := fun i => ⟨a i,h i⟩
      have hab : boxExponent m b=a := by ext i; rfl
      exact (MvPolynomial.mem_support_iff.mp ha) (hab ▸ hf b)
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    refine ⟨Finsupp.single i 2,⟨i,rfl⟩,?_⟩
    intro j
    by_cases hji : j=i
    · subst j
      simpa using hi
    · simp only [Finsupp.single_eq_of_ne hji,zero_le]

 def boxCoeff (b : Box m) : Parameters A m →ₗ[A] A :=
  ((squareIdeal A m).restrictScalars A).liftQ (MvPolynomial.lcoeff A (boxExponent m b))
    (by intro f hf; exact (squareIdeal_coeff_iff A m f).mp hf b)

@[simp] theorem boxCoeff_mk (b : Box m) (f : MvPolynomial (Fin m) A) :
    boxCoeff A m b (Ideal.Quotient.mk (squareIdeal A m) f)=f.coeff (boxExponent m b) := rfl

 theorem parameters_ext (x y : Parameters A m)
    (h : ∀ b,boxCoeff A m b x=boxCoeff A m b y) : x=y := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective y
  apply sub_eq_zero.mp
  rw [←map_sub,Ideal.Quotient.eq_zero_iff_mem,squareIdeal_coeff_iff]
  intro b
  rw [MvPolynomial.coeff_sub,sub_eq_zero]
  exact h b

variable {A m} {B : Type*} [CommRing B]

@[simp] theorem boxCoeff_mapParameters (f : A →+* B) (b : Box m) (x : Parameters A m) :
    boxCoeff B m b (mapParameters f x)=f (boxCoeff A m b x) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change (MvPolynomial.map f p).coeff (boxExponent m b)=f (p.coeff (boxExponent m b))
  exact MvPolynomial.coeff_map _ _ _

 theorem mapParameters_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (mapParameters (m:=m) f) := by
  intro x y h
  apply parameters_ext A m x y
  intro b
  apply hf
  rw [←boxCoeff_mapParameters,←boxCoeff_mapParameters,h]

variable (A m)

def boxMonomial (b : Box m) : Parameters A m :=
  Ideal.Quotient.mk (squareIdeal A m) (MvPolynomial.monomial (boxExponent m b) 1)

@[simp] theorem boxCoeff_boxMonomial (b c : Box m) :
    boxCoeff A m b (boxMonomial A m c)=if b=c then 1 else 0 := by
  classical
  simp only [boxMonomial,boxCoeff_mk,MvPolynomial.coeff_monomial,
    (boxExponent_injective m).eq_iff,eq_comm]

 theorem sum_boxMonomial (x : Parameters A m) :
    (∑ b : Box m,boxCoeff A m b x • boxMonomial A m b)=x := by
  apply parameters_ext A m
  intro b
  simp only [map_sum,map_smul,boxCoeff_boxMonomial,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp

 
def boxSeries {σ : Type*} (b : Box m) (f : MvPowerSeries σ (Parameters A m)) : MvPowerSeries σ A :=
  fun d => boxCoeff A m b (MvPowerSeries.coeff d f)

@[simp] theorem coeff_boxSeries {σ : Type*} (b : Box m)
    (f : MvPowerSeries σ (Parameters A m)) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (boxSeries A m b f)=boxCoeff A m b (MvPowerSeries.coeff d f) := rfl

 theorem sum_boxSeries {σ : Type*} (f : MvPowerSeries σ (Parameters A m)) :
    (∑ b : Box m,MvPowerSeries.C (boxMonomial A m b)*
      MvPowerSeries.map (algebraMap A (Parameters A m)) (boxSeries A m b f))=f := by
  ext d
  simp only [map_sum,MvPowerSeries.coeff_C_mul,MvPowerSeries.coeff_map,coeff_boxSeries]
  calc
    _ = ∑ b : Box m,boxCoeff A m b (MvPowerSeries.coeff d f) • boxMonomial A m b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_comm]
      exact (Algebra.smul_def (R:=A) _ _).symm
    _ = _ := sum_boxMonomial A m (MvPowerSeries.coeff d f)

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
open scoped BigOperators
variable {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}

@[simp] theorem map_boxMonomial (f : A →+* B) (b : Box m) :
    mapParameters f (boxMonomial A m b)=boxMonomial B m b := by
  change Ideal.Quotient.mk (squareIdeal B m) (MvPolynomial.map f (MvPolynomial.monomial _ 1))=_
  rw [MvPolynomial.map_monomial,map_one]
  rfl

 theorem sub_constant_parameters_mem (a : Parameters A m) :
    a-algebraMap A (Parameters A m) (augmentation A m a)∈parameterIdeal A m := by
  refine Quotient.inductionOn' a ?_
  intro p
  change Ideal.Quotient.mk (squareIdeal A m) p -
    algebraMap A (Parameters A m) (augmentation A m (Ideal.Quotient.mk (squareIdeal A m) p))∈_
  induction p using MvPolynomial.induction_on with
  | C c =>
    change algebraMap A (Parameters A m) c-algebraMap A (Parameters A m)
      (augmentation A m (algebraMap A (Parameters A m) c))∈_
    simp
  | add p q hp hq =>
    simpa only [map_add,add_sub_add_comm] using (parameterIdeal A m).add_mem hp hq
  | mul_X p i _ =>
    simp only [map_mul,show Ideal.Quotient.mk (squareIdeal A m) (MvPolynomial.X i)=parameter A m i from rfl,
      augmentation_parameter,mul_zero,map_zero,sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

 theorem augmentation_eq_zero_of_mem {a : Parameters A m} (ha : a∈parameterIdeal A m) :
    augmentation A m a=0 := by
  have hh : parameterIdeal A m≤RingHom.ker (augmentation A m) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact augmentation_parameter A m i
  exact hh ha

 theorem mem_parameterIdeal_iff (a : Parameters A m) :
    a∈parameterIdeal A m ↔ augmentation A m a=0 := by
  constructor
  · exact augmentation_eq_zero_of_mem
  · intro ha
    simpa only [ha,map_zero,sub_zero] using sub_constant_parameters_mem a

 theorem mapParameters_mem_iff (f : A →+* B) (hf : Function.Injective f)
    (a : Parameters A m) : mapParameters f a∈parameterIdeal B m ↔ a∈parameterIdeal A m := by
  simp only [mem_parameterIdeal_iff,augmentation_mapParameters]
  exact (map_eq_zero_iff f hf)

variable {K σ : Type*} [Field K] (R : Subring K)

 
def liftParameterSeries (f : MvPowerSeries σ (Parameters K m))
    (hf : ∀ b d,MvPowerSeries.coeff d (boxSeries K m b f)∈R) :
    MvPowerSeries σ (Parameters R m) :=
  ∑ b : Box m,MvPowerSeries.C (boxMonomial R m b)*
    MvPowerSeries.map (algebraMap R (Parameters R m))
      (MvPowerSeries.toSubring (boxSeries K m b f) R (hf b))

 theorem map_liftParameterSeries (f : MvPowerSeries σ (Parameters K m))
    (hf : ∀ b d,MvPowerSeries.coeff d (boxSeries K m b f)∈R) :
    MvPowerSeries.map (mapParameters R.subtype) (liftParameterSeries R f hf)=f := by
  calc
    _ = ∑ b : Box m,MvPowerSeries.C (boxMonomial K m b)*
        MvPowerSeries.map (algebraMap K (Parameters K m)) (boxSeries K m b f) := by
      rw [liftParameterSeries,map_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul,MvPowerSeries.map_C,map_boxMonomial]
      congr 1
      ext d
      simp only [MvPowerSeries.coeff_map,mapParameters_algebraMap]
      rfl
    _ = f := sum_boxSeries K m f

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
universe u
variable (A : Type*) [CommRing A] {l : ℕ} (σ : Fin l → Type u)
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)] (m : ℕ)

abbrev Triple := {p : Fin m × Fin m × Fin m //
  p.1≠p.2.1 ∧ p.1≠p.2.2 ∧ p.2.1≠p.2.2}

 

structure TensorPrimitives {d c : ℕ} {e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c}
    {active : Fin m ↪ Fin l} (M : TensorModel A σ m d c e active) where
  left : Triple m → ((i : Fin l) × σ i) → MvPowerSeries (Fin d) (Parameters A m)
  right : Triple m → ((i : Fin l) × σ i) → MvPowerSeries (Fin c) A
  left_eq : ∀ q, (∑ v,left q v*MvPowerSeries.subst M.H
      (MvPowerSeries.pderiv v (deformed A σ m M.F active M.b)))=
    MvPowerSeries.C (parameter A m q.val.1*parameter A m q.val.2.1*parameter A m q.val.2.2)
  right_eq : ∀ q, (∑ v,right q v*MvPowerSeries.subst M.G
      (MvPowerSeries.pderiv v (potential A σ M.F)))=
    MvPowerSeries.subst M.G (perturbation A σ m active M.b q.val.1*
      perturbation A σ m active M.b q.val.2.1*perturbation A σ m active M.b q.val.2.2)

 

theorem exists_tensorPrimitives {d c : ℕ} {e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c}
    {active : Fin m ↪ Fin l} (M : TensorModel A σ m d c e active) :
    Nonempty (TensorPrimitives A σ m M) := by
  classical
  have hL : ∀ q : Triple m, ∃ a : ((i : Fin l) × σ i) → _,
      (∑ v,a v*MvPowerSeries.subst M.H
        (MvPowerSeries.pderiv v (deformed A σ m M.F active M.b)))=
      MvPowerSeries.C (parameter A m q.val.1*parameter A m q.val.2.1*parameter A m q.val.2.2) := by
    intro q
    exact Ideal.mem_span_range_iff_exists_fun.mp
      (M.left_triple _ _ _ q.property.1 q.property.2.1 q.property.2.2)
  have hR : ∀ q : Triple m, ∃ a : ((i : Fin l) × σ i) → _,
      (∑ v,a v*MvPowerSeries.subst M.G (MvPowerSeries.pderiv v (potential A σ M.F)))=
      MvPowerSeries.subst M.G (perturbation A σ m active M.b q.val.1*
        perturbation A σ m active M.b q.val.2.1*perturbation A σ m active M.b q.val.2.2) := by
    intro q
    exact Ideal.mem_span_range_iff_exists_fun.mp
      (M.right_triple _ _ _ q.property.1 q.property.2.1 q.property.2.2)
  choose L hL using hL
  choose R hR using hR
  exact ⟨⟨L,R,hL,hR⟩⟩

end
end PD4Tensor.Spreading
end

end OAI
