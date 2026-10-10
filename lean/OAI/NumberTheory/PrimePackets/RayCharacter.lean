import Mathlib
import OAI.NumberTheory.PrimePackets.PrincipalUnits

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction

 

lemma quotient_isUnit_iff_span_coprime {R : Type*} [CommRing R]
    (M : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span {a}) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have he : a * b - 1 ∈ M := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [map_sub, map_mul, map_one, hb, sub_self]
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : a * b ∈ Ideal.span {a} ⊔ M :=
      Submodule.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right a b))
    have hm : a * b - 1 ∈ Ideal.span {a} ⊔ M := Submodule.mem_sup_right he
    simpa only [sub_sub_cancel] using (Ideal.span {a} ⊔ M).sub_mem hmem hm
  · intro h
    have h1 : (1 : R) ∈ Ideal.span {a} ⊔ M := by rw [h]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have he := congrArg (Ideal.Quotient.mk M) hxy
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] using he

variable {K : Type*} [Field K] [NumberField K]

 

structure EvenRayCharacter (K : Type*) [Field K] [NumberField K] (N : ℕ) where
  idealHom : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂˣ
  finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ J, idealHom J ^ e = 1
  residue : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ
  principalLaw : ∀ (a : 𝓞 K) (ha : a ≠ 0),
    IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) →
    (idealHom (integralIdealFractionalUnit (Ideal.span {a})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha)) : ℂ) =
        residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)

namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)

lemma idealHom_norm (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ‖(ψ.idealHom J : ℂ)‖ = 1 := by
  obtain ⟨e, he, hpow⟩ := ψ.finiteOrder
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hpow J)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H

 

lemma residue_unit (z : (𝓞 K)ˣ) :
    ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z : 𝓞 K)) = 1 := by
  have hspan : Ideal.span {(z : 𝓞 K)} = ⊤ := Ideal.span_singleton_eq_top.mpr z.isUnit
  have hcop : IsCoprime (Ideal.span {(z : 𝓞 K)}) (rationalModulusIdeal (𝓞 K) N) := by
    rw [hspan, ← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.principalLaw (z : 𝓞 K) z.ne_zero hcop
  simpa only [hspan, integralIdealFractionalUnit_top, map_one, Units.val_one] using H.symm

 

def underlyingIdeal (J : integralFractionalIdeals K) : Ideal (𝓞 K) :=
  ((integralFractionalIdealsEquiv K).symm J).val

lemma underlyingIdeal_ne_bot (J : integralFractionalIdeals K) :
    underlyingIdeal J ≠ ⊥ := ((integralFractionalIdealsEquiv K).symm J).property

lemma underlyingIdeal_coe (J : integralFractionalIdeals K) :
    (underlyingIdeal J : FractionalIdeal (𝓞 K)⁰ K) = J.val.val := by
  have H := (integralFractionalIdealsEquiv K).apply_symm_apply J
  exact congrArg (fun U : integralFractionalIdeals K => U.val.val) H

lemma underlyingIdeal_unit (J : integralFractionalIdeals K) :
    integralIdealFractionalUnit (underlyingIdeal J) (underlyingIdeal_ne_bot J) = J.val := by
  apply Units.ext
  exact underlyingIdeal_coe J

 

lemma generator_principal_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} =
      I * underlyingIdeal ⟨J.val, J.property.1⟩ := by
  let U := integralIdealFractionalUnit I hI
  have h := congrArg Subtype.val (idealElementRepresentative_spec U J)
  change relativeElementIdeal U (idealElementRepresentative U J).val = J.val at h
  have hm : J.val * U = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative U J).val := by
    rw [← h]
    simp [relativeElementIdeal]
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative U J)} :
    FractionalIdeal (𝓞 K)⁰ K) = ((I * underlyingIdeal ⟨J.val, J.property.1⟩ : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  have he : algebraMap (𝓞 K) K
      (idealIntegerElement I hI (idealElementRepresentative U J)) =
      ((idealElementRepresentative U J).val : K) := idealIntegerElement_coe I hI _
  rw [he]
  have H := congrArg (fun W : (FractionalIdeal (𝓞 K)⁰ K)ˣ => W.val) hm
  simp only [Units.val_mul, coe_toPrincipalIdeal] at H
  exact H.symm.trans (by erw [underlyingIdeal_coe]; exact mul_comm _ _)

lemma generator_integer_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    idealIntegerElement I hI (idealElementRepresentative _ J) ≠ 0 := by
  intro hz
  have H := idealIntegerElement_coe I hI (idealElementRepresentative _ J)
  rw [hz] at H
  change (0 : K) = _ at H
  exact (idealElementRepresentative _ J).val.ne_zero H.symm

lemma generator_fractional_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    integralIdealFractionalUnit
      (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
        generator_integer_ne_zero I hI J) = integralIdealFractionalUnit I hI * J.val := by
  apply Units.ext
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} :
    FractionalIdeal (𝓞 K)⁰ K) = _
  erw [generator_principal_product, FractionalIdeal.coeIdeal_mul, underlyingIdeal_coe]
  rfl

 

def coefficient (J : integralFractionalIdeals K) : ℂ :=
  if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
  then (ψ.idealHom J.val : ℂ) else 0

lemma coefficient_norm_le_one (J : integralFractionalIdeals K) :
    ‖ψ.coefficient J‖ ≤ 1 := by
  classical
  unfold coefficient
  split_ifs
  · exact (ψ.idealHom_norm J.val).le
  · simp only [norm_zero, zero_le_one]

 

lemma coefficient_eq_residue (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    ψ.coefficient ⟨J.val, J.property.1⟩ =
      ((ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ))⁻¹ *
        idealResidueCoefficient I hI N ψ.residue J := by
  let a := idealIntegerElement I hI (idealElementRepresentative _ J)
  have hid : idealResidueCoefficient I hI N ψ.residue J =
      ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) := rfl
  have hc : IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) ↔
      IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩) (rationalModulusIdeal (𝓞 K) N) := by
    rw [show Ideal.span {a} = I * underlyingIdeal ⟨J.val, J.property.1⟩ from
      generator_principal_product I hI J, IsCoprime.mul_left_iff, and_iff_right hcop]
  change (if IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩)
    (rationalModulusIdeal (𝓞 K) N) then (ψ.idealHom J.val : ℂ) else 0) = _
  erw [hid]
  by_cases hJ : IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩)
      (rationalModulusIdeal (𝓞 K) N)
  · rw [ite_eq_left hJ, ← ψ.principalLaw a (generator_integer_ne_zero I hI J) (hc.mpr hJ),
      generator_fractional_product, map_mul, Units.val_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  · rw [ite_eq_right hJ, ψ.residue.map_nonunit
      (fun hunit => hJ (hc.mp ((quotient_isUnit_iff_span_coprime _ a).mp hunit))), mul_zero]

 
def dirichlet (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)

lemma dirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)) := by
  apply Summable.of_norm_bounded (HeckeMellin.integralFractionalIdeals_norm_summable hs)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (ψ.coefficient_norm_le_one J)

 

def classIdeal (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N)
    (by simp [rationalModulusIdeal, NeZero.ne N]) c

lemma classIdeal_ne_bot [NeZero N] (c : ClassGroup (𝓞 K)) :
    (classIdeal K N c).val ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.mp (classIdeal K N c).property

lemma classIdeal_coprime [NeZero N] (c : ClassGroup (𝓞 K)) :
    IsCoprime (classIdeal K N c).val (rationalModulusIdeal (𝓞 K) N) :=
  (coprimeClassRepresentative_spec _ _ c).1

lemma classIdeal_class [NeZero N] (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (integralIdealFractionalUnit (classIdeal K N c).val
      (classIdeal_ne_bot c)) = c := by
  change ClassGroup.mk K (FractionalIdeal.mk0 K (classIdeal K N c)) = c
  rw [ClassGroup.mk_mk0]
  exact (coprimeClassRepresentative_spec _ _ c).2

 

def classPartition [NeZero N] :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber
      (integralIdealFractionalUnit (classIdeal K N c).val (classIdeal_ne_bot c))) ≃
        integralFractionalIdeals K where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1, J.2, by rw [classIdeal_class, inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c, J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by
      rw [J.2.2, classIdeal_class, inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x =
        (ClassGroup.mk K (integralIdealFractionalUnit
          (classIdeal K N ((ClassGroup.mk K J.val)⁻¹)).val
          (classIdeal_ne_bot _)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl

variable [NeZero N]

 

def continued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    ((ψ.idealHom (integralIdealFractionalUnit
      (classIdeal K N c).val (classIdeal_ne_bot c)) : ℂ))⁻¹ *
        residueIdealContinued σ (classIdeal K N c).val (classIdeal_ne_bot c) N ψ.residue s

 

theorem continued_entire {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) : Differentiable ℂ (ψ.continued σ) := by
  unfold continued
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.const_mul
  exact residueIdealContinued_entire σ hn (classIdeal K N c).val
    (classIdeal_ne_bot c) N (classIdeal_coprime c) ψ.residue hψ

 

theorem continued_eq_dirichlet {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    ψ.continued σ s = ψ.dirichlet s := by
  let F := fun J : integralFractionalIdeals K => ψ.coefficient J *
    ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)
  have H := ((classPartition (K := K) (N := N)).summable_iff.mpr
    (ψ.dirichlet_summable hs)).tsum_sigma
  change (∑' x, F (classPartition (K := K) (N := N) x)) = _ at H
  rw [(classPartition (K := K) (N := N)).tsum_eq F] at H
  simp only [tsum_fintype] at H
  unfold continued dirichlet
  rw [show (∑' J, F J) = _ from H]
  apply Finset.sum_congr rfl
  intro c _
  rw [residueIdealContinued_eq_series σ hn _ _ N ψ.residue hψ ψ.residue_unit hs,
    ← tsum_mul_left]
  apply tsum_congr
  intro J
  change _ = ψ.coefficient ⟨J.val, J.property.1⟩ * _
  erw [ψ.coefficient_eq_residue _ _ (classIdeal_coprime c) J]
  exact (mul_assoc _ _ _).symm

omit [NeZero N] in
lemma coefficient_unit : ψ.coefficient (unitIntegralIdeal K) = 1 := by
  have hi : underlyingIdeal (unitIntegralIdeal K) = ⊤ := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change (underlyingIdeal (unitIntegralIdeal K) : FractionalIdeal (𝓞 K)⁰ K) =
      (⊤ : Ideal (𝓞 K))
    rw [underlyingIdeal_coe, FractionalIdeal.coeIdeal_top]
    rfl
  have hcop : IsCoprime (underlyingIdeal (unitIntegralIdeal K))
      (rationalModulusIdeal (𝓞 K) N) := by
    rw [hi, ← Ideal.one_eq_top]
    exact isCoprime_one_left
  change (if IsCoprime (underlyingIdeal (unitIntegralIdeal K))
    (rationalModulusIdeal (𝓞 K) N) then _ else _) = _
  rw [ite_eq_left hcop]
  change (ψ.idealHom 1 : ℂ) = 1
  simp

 

omit [NeZero N] in
theorem dirichlet_tendsto_atTop :
    Filter.Tendsto (fun s : ℝ => ψ.dirichlet s) Filter.atTop (nhds 1) := by
  let g := fun J : integralFractionalIdeals K =>
    if J = unitIntegralIdeal K then (1 : ℂ) else 0
  have hg : (∑' J, g J) = 1 := by simp [g]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence
    (integralFractionalIdeals_norm_summable (K := K) (s := 2) (by norm_num))
  · intro J
    by_cases hJ : J = unitIntegralIdeal K
    · subst J
      rw [show g (unitIntegralIdeal K) = 1 from ite_eq_left rfl]
      rw [ψ.coefficient_unit]
      simp [unitIntegralIdeal]
    · have H : 1 < (FractionalIdeal.absNorm J.1.val : ℝ) :=
        lt_of_le_of_ne (integralFractionalIdeals_absNorm_ge_one J)
          (Ne.symm ((integralFractionalIdeals_absNorm_eq_one_iff J).not.mpr hJ))
      have HR := (tendsto_rpow_atBot_of_base_gt_one
        (FractionalIdeal.absNorm J.1.val : ℝ) H).comp tendsto_neg_atTop_atBot
      have HC := (Complex.continuous_ofReal.tendsto 0).comp HR
      have HC' := tendsto_const_nhds.mul HC (a := ψ.coefficient J)
      simpa only [Function.comp_apply, g, ite_eq_right hJ, Complex.ofReal_zero, mul_zero,
        Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le, Complex.ofReal_neg] using HC'
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with s hs J
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
      Complex.neg_re, Complex.ofReal_re]
    exact (mul_le_of_le_one_left
      (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _) (ψ.coefficient_norm_le_one J)).trans
        (Real.rpow_le_rpow_of_exponent_le
          (integralFractionalIdeals_absNorm_ge_one J) (neg_le_neg hs))

lemma continued_tendsto_atTop {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) :
    Filter.Tendsto (fun s : ℝ => ψ.continued σ s) Filter.atTop (nhds 1) := by
  apply ψ.dirichlet_tendsto_atTop.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with s hs
  exact (ψ.continued_eq_dirichlet σ hn hψ hs).symm

lemma continued_ne_zero {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) : ψ.continued σ ≠ 0 := by
  obtain ⟨s,hs⟩ := ((ψ.continued_tendsto_atTop σ hn hψ).eventually_ne
    (one_ne_zero : (1 : ℂ) ≠ 0)).exists
  exact fun H => hs (congrFun H s)

 

theorem continued_finite_nonnegative_order {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.continued σ) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (ψ.continued σ) z :=
    fun z => (ψ.continued_entire σ hn hψ).analyticAt z
  have hfin : analyticOrderAt (ψ.continued σ) β ≠ ⊤ := by
    intro H
    exact ψ.continued_ne_zero σ hn hψ
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

 

def conjugate : EvenRayCharacter K N where
  idealHom := (Units.map ((starRingEnd ℂ).toMonoidHom)).comp ψ.idealHom
  finiteOrder := by
    obtain ⟨e,he,H⟩ := ψ.finiteOrder
    refine ⟨e,he,fun J => ?_⟩
    have h := congrArg (Units.map ((starRingEnd ℂ).toMonoidHom)) (H J)
    simpa only [map_pow, map_one, MonoidHom.comp_apply] using h
  residue := star ψ.residue
  principalLaw := by
    intro a ha hcop
    have H := congrArg conj (ψ.principalLaw a ha hcop)
    exact H

omit [NeZero N] in
@[simp] lemma conjugate_idealHom (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (ψ.conjugate.idealHom J : ℂ) = conj ((ψ.idealHom J : ℂ)) := rfl

omit [NeZero N] in
lemma conjugate_residue_ne_one (hψ : ψ.residue ≠ 1) : ψ.conjugate.residue ≠ 1 := by
  change star ψ.residue ≠ 1
  intro H
  apply hψ
  have HC := congrArg star H
  simpa using HC

omit [NeZero N] in
lemma coefficient_conjugate (J : integralFractionalIdeals K) :
    ψ.conjugate.coefficient J = conj (ψ.coefficient J) := by
  unfold coefficient
  split_ifs
  · exact ψ.conjugate_idealHom J.val
  · exact (map_zero _).symm

omit [NeZero N] in
lemma dirichlet_conj_real (r : ℝ) :
    conj (ψ.dirichlet r) = ψ.conjugate.dirichlet r := by
  unfold dirichlet
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro J
  rw [map_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le, Complex.conj_ofReal,
    ψ.coefficient_conjugate]

 

theorem continued_conjugation {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) (s : ℂ) :
    ψ.conjugate.continued σ (conj s) = conj (ψ.continued σ s) := by
  have H : Differentiable ℂ (conj ∘ ψ.continued σ ∘ conj) := by
    intro z
    apply differentiableAt_conj_conj_iff.mpr
    exact ψ.continued_entire σ hn hψ _
  have HE := entire_eq_of_real_eq H
    (ψ.conjugate.continued_entire σ hn (ψ.conjugate_residue_ne_one hψ)) (fun r hr => by
      simp only [Function.comp_apply, Complex.conj_ofReal]
      rw [ψ.continued_eq_dirichlet σ hn hψ hr,
        ψ.conjugate.continued_eq_dirichlet σ hn (ψ.conjugate_residue_ne_one hψ) hr,
        ψ.dirichlet_conj_real])
  have Hs := congrFun HE (conj s)
  simpa using Hs.symm

 

lemma analyticAt_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (conj z)) : AnalyticAt ℂ (conj ∘ f ∘ conj) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have H := (Complex.continuous_conj.tendsto z).eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp hf)
  filter_upwards [H] with w hw
  exact differentiableAt_conj_conj_iff.mpr hw

lemma iteratedDeriv_reflection (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv m f ∘ conj := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, ← iteratedDeriv_succ]

lemma analyticOrderAt_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderAt (conj ∘ f ∘ conj) z = analyticOrderAt f (conj z) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro m
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_reflection hf),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [iteratedDeriv_reflection, Function.comp_apply, map_eq_zero]

 

theorem continued_order_conjugation {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) (s : ℂ) :
    meromorphicOrderAt (ψ.conjugate.continued σ) (conj s) =
      meromorphicOrderAt (ψ.continued σ) s := by
  have he : ψ.conjugate.continued σ = conj ∘ ψ.continued σ ∘ conj := by
    funext z
    simpa only [Function.comp_apply, Complex.conj_conj] using
      ψ.continued_conjugation σ hn hψ (conj z)
  have ha := (ψ.continued_entire σ hn hψ).analyticAt s
  have hac := (ψ.conjugate.continued_entire σ hn (ψ.conjugate_residue_ne_one hψ)).analyticAt
    (conj s)
  rw [hac.meromorphicOrderAt_eq, ha.meromorphicOrderAt_eq, he]
  congr 1
  simpa only [Complex.conj_conj] using analyticOrderAt_reflection
    (by simpa only [Complex.conj_conj] using ha :
      AnalyticAt ℂ (ψ.continued σ) (conj (conj s)))

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
