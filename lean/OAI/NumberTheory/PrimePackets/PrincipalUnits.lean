import Mathlib
import OAI.NumberTheory.PrimePackets.UnitOrbitIntegrals

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
open scoped BigOperators NumberField ENNReal
open scoped BigOperators NumberField
open scoped BigOperators NumberField ENNReal nonZeroDivisors
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]

lemma integralIdealFractionalUnit_top :
    integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 := by
  apply Units.ext
  simp [integralIdealFractionalUnit]

def principalUnitFiber :
    integralIdealClassFiber (integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot) :=
  ⟨1, le_rfl, by simp [integralIdealFractionalUnit_top]⟩

def principalUnitElement :
    nonzeroIdealElements (integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot) :=
  ⟨1, by simp [integralIdealFractionalUnit_top]⟩

lemma principalUnitElement_class :
    relativeElementClassMap _ (principalUnitElement (K := K)) = principalUnitFiber := by
  apply Subtype.ext
  simp [relativeElementClassMap, principalUnitElement, principalUnitFiber,
    relativeElementIdeal, integralIdealFractionalUnit_top]

lemma idealResidueCoefficient_principalUnit (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1) :
    idealResidueCoefficient (⊤ : Ideal (𝓞 K)) top_ne_bot N χ principalUnitFiber = 1 := by
  rw [← principalUnitElement_class, idealResidueCoefficient_eq_of_generator _ _ _ _ hunit]
  have H : idealIntegerElement (⊤ : Ideal (𝓞 K)) top_ne_bot principalUnitElement = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [idealIntegerElement_coe]
    rfl
  simp [idealResidueElementWeight, H]

 
def principalResidueDirichlet (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber (integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot),
    idealResidueCoefficient ⊤ top_ne_bot N χ J *
      ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s)

 

theorem principalResidueDirichlet_tendsto (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1) :
    Tendsto (fun s : ℝ => principalResidueDirichlet N χ s) atTop (𝓝 1) := by
  classical
  let I := integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot
  let g := fun J : integralIdealClassFiber I =>
    if J = principalUnitFiber then (1:ℂ) else 0
  have hg : (∑' J, g J) = 1 := by simp [g]
  have HR := ENNReal.summable_toReal (idealClass_norm_tsum_ne_top I
    (s := (2:ℝ)) (by norm_num))
  simp only [ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] at HR
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence HR
  · intro J
    by_cases hJ : J = principalUnitFiber
    · subst J
      rw [show g principalUnitFiber = 1 by simp [g]]
      simp only [idealResidueCoefficient_principalUnit N χ hunit]
      simp [principalUnitFiber]
    · have hne : (⟨J.1,J.2.1⟩ : integralFractionalIdeals K) ≠ unitIntegralIdeal K := by
        intro H
        apply hJ
        exact Subtype.ext (congrArg (fun A : integralFractionalIdeals K => A.val) H)
      have H : 1 < (FractionalIdeal.absNorm J.1.val : ℝ) :=
        lt_of_le_of_ne (integralFractionalIdeals_absNorm_ge_one ⟨J.1,J.2.1⟩)
          (Ne.symm ((integralFractionalIdeals_absNorm_eq_one_iff ⟨J.1,J.2.1⟩).not.mpr hne))
      have HR := (tendsto_rpow_atBot_of_base_gt_one
        (FractionalIdeal.absNorm J.1.val : ℝ) H).comp tendsto_neg_atTop_atBot
      have HC := (Complex.continuous_ofReal.tendsto 0).comp HR
      have HC' := tendsto_const_nhds.mul HC
        (a := idealResidueCoefficient ⊤ top_ne_bot N χ J)
      simpa only [Function.comp_apply, g, ite_eq_right hJ, Complex.ofReal_zero, mul_zero,
        Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le, Complex.ofReal_neg] using HC'
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs J
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
      Complex.neg_re, Complex.ofReal_re]
    calc
      _ ≤ (FractionalIdeal.absNorm J.1.val : ℝ)^(-s) :=
        mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
          (idealResidueElementWeight_norm_le_one ⊤ top_ne_bot N χ _)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
        (integralFractionalIdeals_absNorm_ge_one ⟨J.1,J.2.1⟩) (neg_le_neg hs)

 

theorem residuePrincipalContinued_ne_zero {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1) :
    residueIdealContinued σ (⊤ : Ideal (𝓞 K)) top_ne_bot N χ ≠ 0 := by
  have HE : ∀ᶠ s : ℝ in atTop, principalResidueDirichlet N χ s ≠ 0 :=
    (principalResidueDirichlet_tendsto N χ hunit).eventually_ne one_ne_zero
  obtain ⟨s,hs,hL⟩ := ((eventually_gt_atTop (1 : ℝ)).and HE).exists
  intro H
  have He := congrFun H (s : ℂ)
  rw [residueIdealContinued_eq_series σ hn ⊤ top_ne_bot N χ hχ hunit hs] at He
  exact hL He

 

theorem residuePrincipal_finite_nonnegative_order {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt
      (residueIdealContinued σ (⊤ : Ideal (𝓞 K)) top_ne_bot N χ) β = (m : WithTop ℤ) := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (rationalModulusIdeal (𝓞 K) N) := by
    rw [Ideal.isCoprime_iff_codisjoint]
    exact codisjoint_top_left
  have ha : ∀ z, AnalyticAt ℂ
      (residueIdealContinued σ (⊤ : Ideal (𝓞 K)) top_ne_bot N χ) z := fun z =>
    (residueIdealContinued_entire σ hn ⊤ top_ne_bot N hc χ hχ).analyticAt z
  have hfin : analyticOrderAt
      (residueIdealContinued σ (⊤ : Ideal (𝓞 K)) top_ne_bot N χ) β ≠ ⊤ := by
    intro H
    exact residuePrincipalContinued_ne_zero σ hn N χ hχ hunit
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem exists_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, ∀ P ∈ s, x ∉ P * I := by
  classical
  have hex : ∀ P : s, ∃ x ∈ I, x ∉ P.val * I := by
    intro P
    have hP : P.val ≠ 1 := (hprime P P.property).ne_one
    have hne : P.val * I ≠ I := by
      intro H
      apply hP
      exact mul_right_cancel₀ hI (H.trans (one_mul I).symm)
    have hnle : ¬ I ≤ P.val * I := fun H => hne (le_antisymm Ideal.mul_le_right H)
    exact Set.not_subset.mp hnle
  choose x hx hnx using hex
  have he : ∀ P : s, ∃ e : R, ∀ Q : s,
      e - (if Q = P then 1 else 0) ∈ Q.val := by
    intro P
    obtain ⟨e,he⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (fun Q : Ideal R => Q)
      (fun _ => 1) hprime (by intros; assumption)
      (fun Q : s => if Q = P then (1:R) else 0)
    exact ⟨e, fun Q => by simpa using he Q Q.property⟩
  choose e he using he
  refine ⟨∑ P : s, e P * x P, I.sum_mem (fun P _ => I.mul_mem_left _ (hx P)), ?_⟩
  intro Q hQ hmem
  let q : s := ⟨Q,hQ⟩
  have H : (∑ P : s, e P * x P) - x q ∈ Q * I := by
    have Hsum : (∑ P : s, (e P - if q = P then 1 else 0) * x P) ∈ Q * I :=
      (Q * I).sum_mem fun P _ => Ideal.mul_mem_mul (he P q) (hx P)
    convert Hsum using 1
    simp only [sub_mul, Finset.sum_sub_distrib]
    simp
  exact hnx q ((Q * I).sub_mem hmem H |> fun H' => by simpa using H')

lemma exists_nonzero_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, x ≠ 0 ∧ ∀ P ∈ s, x ∉ P * I := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · obtain ⟨x,hx,hx0⟩ := I.ne_bot_iff.mp hI
    exact ⟨x,hx,hx0, by simp⟩
  · obtain ⟨x,hx,H⟩ := exists_simultaneous_ideal_generator I hI s hprime
    refine ⟨x,hx,?_,H⟩
    obtain ⟨P,hP⟩ := hs
    rintro rfl
    exact H P hP (Ideal.zero_mem _)

 

theorem exists_coprime_ideal_product {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    ∃ (x : R) (J : Ideal R), x ≠ 0 ∧ x ∈ I ∧ J ≠ ⊥ ∧
      IsCoprime J M ∧ Ideal.span {x} = I * J := by
  classical
  obtain ⟨x,hx,hx0,Hx⟩ := exists_nonzero_simultaneous_ideal_generator I hI
    (UniqueFactorizationMonoid.factors M).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_factor P
      (Multiset.mem_toFinset.mp hP))
  obtain ⟨J,hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hJ0 : J ≠ ⊥ := by
    intro H
    rw [H, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  refine ⟨x,J,hx0,hx,hJ0,?_,hJ⟩
  apply Ideal.coprime_of_no_prime_ge
  intro P hJP hMP hP
  have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hM hMP
  obtain ⟨Q,hQ,heq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hM
    (Ideal.prime_of_isPrime hP0 hP).irreducible (Ideal.dvd_iff_le.mpr hMP)
  have HPQ : P = Q := associated_iff_eq.mp heq
  subst Q
  apply Hx P (Multiset.mem_toFinset.mpr hQ)
  have hle : Ideal.span {x} ≤ P * I := by
    rw [hJ, mul_comm I J]
    simpa only [mul_comm I J, mul_comm I P] using mul_le_mul_right hJP I
  exact hle (Ideal.subset_span (by simp))

open scoped nonZeroDivisors in
 

theorem exists_coprime_class_representative {R : Type*} [CommRing R]
    [IsDedekindDomain R] (M : Ideal R) (hM : M ≠ ⊥) (c : ClassGroup R) :
    ∃ J : (Ideal R)⁰, IsCoprime J.val M ∧ ClassGroup.mk0 J = c := by
  obtain ⟨I,hI⟩ := ClassGroup.mk0_surjective c⁻¹
  obtain ⟨x,J,hx0,hx,hJ0,hcop,hprod⟩ := exists_coprime_ideal_product I.val M
    (mem_nonZeroDivisors_iff_ne_zero.mp I.property) hM
  let Jn : (Ideal R)⁰ := ⟨J,mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  refine ⟨Jn,hcop,?_⟩
  have H : ClassGroup.mk0 I * ClassGroup.mk0 Jn = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (I * Jn).property).mpr
    change (I.val * J).IsPrincipal
    rw [← hprod]
    infer_instance
  rw [hI] at H
  have He := congrArg (fun z : ClassGroup R => c * z) H
  simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using He

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]

def coprimeClassRepresentative (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (exists_coprime_class_representative M hM c).choose

lemma coprimeClassRepresentative_spec (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) :
    IsCoprime (coprimeClassRepresentative M hM c).val M ∧
      ClassGroup.mk0 (coprimeClassRepresentative M hM c) = c :=
  (exists_coprime_class_representative M hM c).choose_spec

 

theorem exists_residueClassContinued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (c : ClassGroup (𝓞 K)) :
    ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
      IsCoprime I (rationalModulusIdeal (𝓞 K) N) ∧
      ClassGroup.mk K (integralIdealFractionalUnit I hI) = c ∧
      Differentiable ℂ (residueIdealContinued σ I hI N χ) ∧
      ∀ s : ℂ, 1 < s.re →
        residueIdealContinued σ I hI N χ s =
          ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
            idealResidueCoefficient I hI N χ J *
              ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  have hN : rationalModulusIdeal (𝓞 K) N ≠ ⊥ := by
    simp [rationalModulusIdeal, NeZero.ne N]
  let I := coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N) hN c
  have hI : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have HI := coprimeClassRepresentative_spec (rationalModulusIdeal (𝓞 K) N) hN c
  refine ⟨I.val,hI,HI.1,?_,residueIdealContinued_entire σ hn I.val hI N HI.1 χ hχ,?_⟩
  · change ClassGroup.mk K (FractionalIdeal.mk0 K I) = c
    rw [ClassGroup.mk_mk0]
    exact HI.2
  · intro s hs
    exact residueIdealContinued_eq_series σ hn I.val hI N χ hχ hunit hs

end PrimeDegreePackets
end
end

end OAI
