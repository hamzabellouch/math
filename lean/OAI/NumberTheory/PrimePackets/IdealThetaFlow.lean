import Mathlib
import OAI.NumberTheory.PrimePackets.GaussianMellin

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
namespace PrimeDegreePackets
open ThetaConstruction

variable {R : Type*} [CommRing R]

def idealUnitMulEquiv (I : Ideal R) (z : Rˣ) : I ≃ I where
  toFun a := ⟨(z:R)*(a:R), I.mul_mem_left _ a.property⟩
  invFun a := ⟨((z⁻¹:Rˣ):R)*(a:R), I.mul_mem_left _ a.property⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma idealResidueFlowTheta_eq_complex (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) (t : ℝ) :
    idealResidueFlowTheta σ I N χ u t =
      ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a:𝓞 K)) *
        complexFlowGaussian σ ((a:𝓞 K):K) t u := by
  unfold idealResidueFlowTheta complexFlowGaussian
  apply tsum_congr
  intro a
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]

 

lemma idealResidueFlowTheta_unit_covariance [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (I : Ideal (𝓞 K)) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (z : (𝓞 K)ˣ) (u : LogCoordinates d) (t : ℝ) :
    idealResidueFlowTheta σ I N χ u t =
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) *
        idealResidueFlowTheta σ I N χ (orderedUnitLog σ (Additive.ofMul z)+u) t := by
  simp_rw [idealResidueFlowTheta_eq_complex]
  rw [← (idealUnitMulEquiv I z).tsum_eq]
  simp only [idealUnitMulEquiv, Equiv.coe_fn_mk, map_mul,
    complexFlowGaussian_unit_translate, mul_assoc]
  exact tsum_mul_left

lemma idealResidueFlowTheta_congruence_periodic [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (I : Ideal (𝓞 K)) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (z : (𝓞 K)ˣ) (hz : z ∈ rationalCongruenceUnits (𝓞 K) N)
    (u : LogCoordinates d) (t : ℝ) :
    idealResidueFlowTheta σ I N χ (orderedUnitLog σ (Additive.ofMul z)+u) t =
      idealResidueFlowTheta σ I N χ u t := by
  have H := idealResidueFlowTheta_unit_covariance σ I N χ z u t
  rw [(mem_rationalCongruenceUnits N z).mp hz,map_one,one_mul] at H
  exact H.symm

 

def rationalCongruenceLogDomain [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ) [NeZero N] : Set (LogCoordinates d) := by
  letI := rationalCongruenceUnits_finiteIndex (NumberField.RingOfIntegers.basis K) N
  exact ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ
    (orderedLogSubgroup σ (rationalCongruenceUnits (𝓞 K) N))
      (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ (rationalCongruenceUnits (𝓞 K) N))))

lemma rationalCongruenceLogDomain_fundamental [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ) [NeZero N] :
    IsAddFundamentalDomain (orderedLogSubgroup σ (rationalCongruenceUnits (𝓞 K) N))
      (rationalCongruenceLogDomain σ N) volume := by
  let := rationalCongruenceUnits_finiteIndex (NumberField.RingOfIntegers.basis K) N
  exact ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ (rationalCongruenceUnits (𝓞 K) N))) volume

lemma rationalCongruenceLogDomain_measurable [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ) [NeZero N] :
    MeasurableSet (rationalCongruenceLogDomain σ N) := by
  unfold rationalCongruenceLogDomain
  exact ZSpan.fundamentalDomain_measurableSet _

lemma rationalCongruenceLogDomain_bounded [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ) [NeZero N] :
    Bornology.IsBounded (rationalCongruenceLogDomain σ N) := by
  unfold rationalCongruenceLogDomain
  exact ZSpan.fundamentalDomain_isBounded _

 

theorem idealResidueFlowTheta_congruenceAverage_entire [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (fun t => ∫ u in rationalCongruenceLogDomain σ N,
      idealResidueFlowTheta σ I N χ u t)) :=
  idealResidueFlowTheta_boundedAverage_entire σ hn I hI N hcop χ hχ
    (rationalCongruenceLogDomain_measurable σ N) (rationalCongruenceLogDomain_bounded σ N)

 

theorem subgroupUnitGaussian_mellin_lintegral [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1:ℝ)*s/2-1)) *
      ∫⁻ u in D, ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
        ENNReal.ofReal ((2/(d+1:ℝ)) *
          ((1/2:ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^(d+1) *
            |(Algebra.norm ℚ a:ℝ)|^(-s)) := by
  simp_rw [lintegral_arithmeticFlowGaussian_subgroup σ S hD]
  simp_rw [mul_left_comm (ENNReal.ofReal _)
    (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞)]
  rw [lintegral_const_mul' _ _ (by simp),
    HeckeMellin.arithmetic_gaussian_lintegral σ hn ha hs]

end PrimeDegreePackets

open scoped BigOperators NumberField ENNReal
namespace PrimeDegreePackets

lemma complex_tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (hom : A →+ B) (hφ : Function.Surjective hom) [Finite hom.ker]
    (f : B → ℂ) (hs : Summable (fun a => f (hom a))) :
    (∑' a, f (hom a)) = (Nat.card hom.ker : ℂ) * ∑' b, f b := by
  classical
  have H := ((Equiv.sigmaFiberEquiv hom).summable_iff.mpr hs).tsum_sigma
  simp only [Function.comp_apply] at H
  rw [(Equiv.sigmaFiberEquiv hom).tsum_eq (fun a => f (hom a))] at H
  rw [H, ← tsum_mul_left]
  apply tsum_congr
  intro b
  let e1 : {a // hom a = b} ≃ (hom ⁻¹' {b}) :=
    Equiv.subtypeEquivRight (fun a => by simp)
  let e := e1.trans (AddMonoidHom.fiberEquivKerOfSurjective hφ b)
  let := Fintype.ofFinite hom.ker
  let := Fintype.ofEquiv hom.ker e.symm
  calc
    (∑' a : {a // hom a = b}, f (hom a)) = ∑' _a : {a // hom a = b}, f b := by
      apply tsum_congr
      intro a
      rw [a.property]
    _ = (Nat.card hom.ker : ℂ) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem integral_tsum_addHom_fundamentalDomain_complex {d : ℕ} {A : Type*}
    [AddGroup A] [Countable A] (L : Submodule ℤ (Fin d → ℝ)) [Countable L]
    (hom : A →+ L) (hφ : Function.Surjective hom) [Finite hom.ker]
    {D : Set (Fin d → ℝ)} (hD : IsAddFundamentalDomain L D volume)
    (f : (Fin d → ℝ) → ℂ) (hfM : Measurable f) (hf : Integrable f) :
    (∫ u in D, ∑' a, f ((hom a : Fin d → ℝ)+u)) =
      (Nat.card hom.ker : ℂ) * ∫ u, f u := by
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  have HI (a : A) : IntegrableOn (fun u => f ((hom a : Fin d → ℝ)+u)) D :=
    (hf.comp_add_left _).restrict
  have HN : (∑' a : A, ∫⁻ u in D, ‖f ((hom a : Fin d → ℝ)+u)‖ₑ) ≠ ⊤ := by
    have HM (a : A) : AEMeasurable (fun u : Fin d → ℝ =>
        ‖f ((hom a : Fin d → ℝ)+u)‖ₑ) (volume.restrict D) :=
      ((hfM.comp (measurable_const.add measurable_id)).enorm).aemeasurable
    rw [← lintegral_tsum HM]
    have HU := lintegral_tsum_addHom_fundamentalDomain L hom hφ hD
      (fun u => ‖f u‖ₑ) hfM.enorm
    rw [HU]
    exact ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne
  have HS : Summable (fun a : A => ∫ u in D, f ((hom a : Fin d → ℝ)+u)) := by
    apply (ENNReal.summable_toReal HN).of_norm_bounded
    intro a
    rw [← integral_norm_eq_lintegral_enorm (HI a).aestronglyMeasurable]
    exact norm_integral_le_integral_norm _
  rw [integral_tsum (fun a => (HI a).aestronglyMeasurable) HN,
    complex_tsum_comp_surjective_addHom hom hφ
      (fun p => ∫ u in D, f ((p : Fin d → ℝ)+u)) HS]
  congr 1
  exact (hD.integral_eq_tsum'' f hf).symm

variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

 

lemma integral_complexFlowGaussian_subgroup
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)} (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (a : K) (t : ℝ) (hG : Integrable (complexFlowGaussian σ a t)) :
    (∫ u in D, ∑' z : S, complexFlowGaussian σ ((z.val:K)*a) t u) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
        ∫ u, complexFlowGaussian σ a t u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (Additive S) := by change Countable S; infer_instance
  let : Countable (orderedLogSubgroup σ S) := (subgroupUnitLogOnto_surjective σ S).countable
  have HM : Measurable (complexFlowGaussian σ a t) := by
    unfold complexFlowGaussian
    have HW := continuous_logFlowWeights (d := d)
    fun_prop
  simp_rw [complexFlowGaussian_unit_translate]
  exact integral_tsum_addHom_fundamentalDomain_complex (orderedLogSubgroup σ S)
    (subgroupUnitLogOnto σ S) (subgroupUnitLogOnto_surjective σ S) hD
    (complexFlowGaussian σ a t) HM hG

end PrimeDegreePackets

open scoped BigOperators NumberField
namespace PrimeDegreePackets
open HeckeMellin
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma complexFlowGaussian_eq_ofReal
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) (u : LogCoordinates d) :
    complexFlowGaussian σ a t u =
      (Real.exp (-Real.pi*t*∑ i, (logFlowWeights u i*σ i a)^2) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold complexFlowGaussian
  congr 1
  push_cast
  ring

omit [NumberField K] in
lemma radialKernel_eq_complexFlowGaussian (σ : OrderedEmbeddings (d+1) K)
    (a : K) (s : ℂ) (t : ℝ) (u : LogCoordinates d) :
    radialKernel s Real.pi (fun i => σ i a) t u =
      (t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) * complexFlowGaussian σ a t u := by
  rw [radialKernel, logEnergy_embeddings]
  unfold complexFlowGaussian
  congr 2
  push_cast
  ring

omit [NumberField K] in
lemma complexFlowGaussian_ae_integrable (σ : OrderedEmbeddings (d+1) K)
    {a : K} (ha : a ≠ 0) :
    ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), Integrable (complexFlowGaussian σ a t) := by
  have H := (integrable_radialKernel_product (s := (2:ℂ)) (by norm_num)
    Real.pi_pos (fun i => σ i a) (fun i => (map_ne_zero (σ i)).mpr ha)).prod_right_ae
  filter_upwards [H,ae_restrict_mem measurableSet_Ioi] with t ht ht0
  simp only [radialKernel_eq_complexFlowGaussian] at ht
  apply (integrable_const_mul_iff (c := (t:ℂ)^(((d+1:ℕ):ℂ)*2/2-1))
    (isUnit_iff_ne_zero.mpr (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht0))))) _).mp
  exact ht

 

theorem subgroupUnitGaussian_mellin [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, (t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
      ∫ u in D, ∑' z : S, complexFlowGaussian σ ((z.val:K)*a) t u) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
        ((2/(d+1:ℂ)) *
          ((1/2:ℂ)*(Real.pi:ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
            ((|(Algebra.norm ℚ a:ℝ)|:ℝ):ℂ)^(-s)) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
        ((Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
          ∫ u, complexFlowGaussian σ a t u) := by
      apply integral_congr_ae
      filter_upwards [complexFlowGaussian_ae_integrable σ ha] with t ht
      rw [integral_complexFlowGaussian_subgroup σ S hD a t ht]
    _ = (Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
        (∫ t : ℝ in Ioi 0, (t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
          ∫ u, complexFlowGaussian σ a t u) := by
      conv_rhs => rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = _ := by
      simp_rw [complexFlowGaussian_eq_ofReal]
      rw [arithmetic_gaussian_mellin σ hn ha hs]

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]

 
def idealIntegerElement (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : 𝓞 K :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose

lemma idealIntegerElement_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    (idealIntegerElement I hI a : K) = (a.val:K) :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.2

lemma idealIntegerElement_unitAction (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealIntegerElement I hI (idealElementUnitAction _ z a) =
      (z:𝓞 K)*idealIntegerElement I hI a := by
  apply NumberField.RingOfIntegers.coe_injective
  simp only [idealIntegerElement_coe,map_mul]
  rfl

def idealResidueElementWeight (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : ℂ :=
  χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (idealIntegerElement I hI a))

lemma idealResidueElementWeight_unitAction (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealResidueElementWeight I hI N χ (idealElementUnitAction _ z a) =
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) *
        idealResidueElementWeight I hI N χ a := by
  simp only [idealResidueElementWeight,idealIntegerElement_unitAction,map_mul]

lemma idealResidueElementWeight_congruence (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI))
    (z : rationalCongruenceUnits (𝓞 K) N) :
    idealResidueElementWeight I hI N χ (idealElementUnitAction _ z.val a) =
      idealResidueElementWeight I hI N χ a := by
  rw [idealResidueElementWeight_unitAction,
    (mem_rationalCongruenceUnits N z.val).mp z.property,map_one,one_mul]

 
def idealResidueCoefficient (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) : ℂ :=
  idealResidueElementWeight I hI N χ (idealElementRepresentative _ J)

 

lemma idealResidueCoefficient_eq_of_generator (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    idealResidueCoefficient I hI N χ (relativeElementClassMap _ a) =
      idealResidueElementWeight I hI N χ a := by
  obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq _
    (idealElementRepresentative _ (relativeElementClassMap _ a)) a
    (idealElementRepresentative_spec _ _)
  conv_rhs => rw [← hz,idealResidueElementWeight_unitAction,hunit,one_mul]
  rfl

lemma finiteMulChar_norm_le_one {R : Type*} [CommRing R] [Finite R]
    (χ : MulChar R ℂ) (a : R) : ‖χ a‖ ≤ 1 := by
  classical
  by_cases h : IsUnit a
  · obtain ⟨z,rfl⟩ := h
    have H : ‖χ (z:R)‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _)
        (Nat.card_pos (α := Rˣ)).ne').mp ?_
      rw [← norm_pow,← map_pow,← Units.val_pow_eq_pow_val,pow_card_eq_one',
        Units.val_one,map_one,norm_one]
    exact H.le
  · rw [χ.map_nonunit h,norm_zero]
    exact zero_le_one

lemma idealResidueElementWeight_norm_le_one (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    ‖idealResidueElementWeight I hI N χ a‖ ≤ 1 := by
  let : Finite ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) :=
    Finite.of_equiv (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin N)
      (integralResidueEquiv (NumberField.RingOfIntegers.basis K) N)
  exact finiteMulChar_norm_le_one χ _

lemma idealResidueCoefficient_summable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber (integralIdealFractionalUnit I hI) =>
      idealResidueCoefficient I hI N χ J *
        ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s)) := by
  have HR := ENNReal.summable_toReal (idealClass_norm_tsum_ne_top
    (integralIdealFractionalUnit I hI) hs)
  simp only [ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] at HR
  apply HR.of_norm_bounded
  intro J
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (idealResidueElementWeight_norm_le_one I hI N χ _)

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma measurable_complexFlowGaussian_joint (σ : OrderedEmbeddings (d+1) K) (a : K) :
    Measurable (fun p : ℝ × LogCoordinates d => complexFlowGaussian σ a p.1 p.2) := by
  unfold complexFlowGaussian
  have HW := continuous_logFlowWeights (d := d)
  fun_prop

omit [NumberField K] in
lemma enorm_complexFlowGaussian (σ : OrderedEmbeddings (d+1) K)
    (a : K) (t : ℝ) (u : LogCoordinates d) :
    ‖complexFlowGaussian σ a t u‖ₑ = arithmeticFlowGaussian σ a t u := by
  rw [← ofReal_norm,complexFlowGaussian_eq_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rfl

 
def unitOrbitMellinKernel (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ)
    (a : K) (s : ℂ) (p : ℝ × LogCoordinates d) : ℂ :=
  (p.1:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
    ∑' z : S, complexFlowGaussian σ ((z.val:K)*a) p.1 p.2

lemma measurable_unitOrbitMellinKernel (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) (a : K) (s : ℂ) :
    Measurable (unitOrbitMellinKernel σ S a s) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  unfold unitOrbitMellinKernel
  apply Measurable.mul (by fun_prop)
  apply Measurable.tsum
  intro z
  exact measurable_complexFlowGaussian_joint σ _

omit [NumberField K] in
lemma enorm_unitOrbitMellinKernel_le (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) (a : K) (s : ℂ) {t : ℝ} (ht : 0 < t)
    (u : LogCoordinates d) :
    ‖unitOrbitMellinKernel σ S a s (t,u)‖ₑ ≤
      ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) *
        ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u := by
  unfold unitOrbitMellinKernel
  rw [enorm_mul]
  have HE : ‖(t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1)‖ₑ =
      ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) := by
    rw [← ofReal_norm,Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  rw [HE]
  refine mul_le_mul' le_rfl ?_
  calc
    _ ≤ ∑' z : S, ‖complexFlowGaussian σ ((z.val:K)*a) t u‖ₑ :=
      enorm_tsum_le_tsum_enorm
    _ = _ := by simp_rw [enorm_complexFlowGaussian]

lemma lintegral_enorm_unitOrbitMellinKernel_le [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫⁻ p, ‖unitOrbitMellinKernel σ S a s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≤
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
        ENNReal.ofReal (realHeckeFactor (d+1) s.re * |(Algebra.norm ℚ a:ℝ)|^(-s.re)) := by
  rw [lintegral_prod _ (measurable_unitOrbitMellinKernel σ S a s).enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ∫⁻ u in D,
        ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) *
          ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lintegral_mono (fun u => enorm_unitOrbitMellinKernel_le σ S a s ht u)
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [subgroupUnitGaussian_mellin_lintegral σ hn S hD ha hs]
      simp only [realHeckeFactor,Nat.cast_add,Nat.cast_one]

 

theorem integrable_unitOrbitMellinKernel [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    Integrable (unitOrbitMellinKernel σ S a s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict D)) := by
  refine ⟨(measurable_unitOrbitMellinKernel σ S a s).aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖unitOrbitMellinKernel σ S a s p‖ₑ
    ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) < ⊤
  rw [lintegral_prod _ (measurable_unitOrbitMellinKernel σ S a s).enorm.aemeasurable]
  apply lt_of_le_of_lt
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact lintegral_mono (fun u => enorm_unitOrbitMellinKernel_le σ S a s ht u)
  · simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [subgroupUnitGaussian_mellin_lintegral σ hn S hD ha hs]
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top

 
theorem integral_unitOrbitMellinKernel [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ p, unitOrbitMellinKernel σ S a s p
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
        ((2/(d+1:ℂ)) *
          ((1/2:ℂ)*(Real.pi:ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
            ((|(Algebra.norm ℚ a:ℝ)|:ℝ):ℂ)^(-s)) := by
  rw [integral_prod _ (integrable_unitOrbitMellinKernel σ hn S hD ha hs)]
  simp only [unitOrbitMellinKernel,integral_const_mul]
  exact subgroupUnitGaussian_mellin σ hn S hD ha hs

end PrimeDegreePackets
end
end

end OAI
