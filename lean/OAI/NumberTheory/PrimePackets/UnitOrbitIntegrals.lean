import Mathlib
import OAI.NumberTheory.PrimePackets.IdealThetaFlow

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
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

lemma tsum_lintegral_unitOrbitMellinKernel_ne_top
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤ := by
  let C : ℝ≥0∞ := (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
    ENNReal.ofReal (realHeckeFactor (d+1) s.re * (FractionalIdeal.absNorm I.val:ℝ)^(-s.re))
  have HJ (J : integralIdealClassFiber I) :
      (∫⁻ p, ‖unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≤
      C * ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val:ℝ)^(-s.re)) := by
    have H := lintegral_enorm_unitOrbitMellinKernel_le σ hn S hD
      (idealElementRepresentative I J).1.ne_zero (lt_trans zero_lt_one hs)
    rw [idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le,
      ← mul_assoc,ENNReal.ofReal_mul (mul_nonneg
        (realHeckeFactor_nonneg _ (lt_trans zero_lt_one hs))
        (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _)),← mul_assoc] at H
    exact H
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum HJ)
  rw [ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top _ (idealClass_norm_tsum_ne_top I hs)
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

lemma tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (tsum_lintegral_unitOrbitMellinKernel_ne_top σ hn I S hD hs)
  apply ENNReal.tsum_le_tsum
  intro J
  apply lintegral_mono
  intro p
  dsimp only
  rw [enorm_mul]
  apply mul_le_of_le_one_left (by positivity)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr (hw J)

 

theorem integral_weightedIdealUnitOrbits
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ p, ∑' J : integralIdealClassFiber I,
      w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℂ) *
        ((2/(d+1:ℂ)) *
          ((1/2:ℂ)*(Real.pi:ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1)) *
        ((FractionalIdeal.absNorm I.val:ℝ):ℂ)^(-s) *
          ∑' J : integralIdealClassFiber I,
            w J * ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  rw [integral_tsum (fun J =>
    ((measurable_unitOrbitMellinKernel σ S _ s).const_mul (w J)).aestronglyMeasurable)
    (tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top σ hn I S hD w hw hs)]
  simp_rw [integral_const_mul,
    integral_unitOrbitMellinKernel σ hn S hD (idealElementRepresentative I _).1.ne_zero
      (lt_trans zero_lt_one hs),idealElementRepresentative_absNorm,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (fractionalIdeal_absNorm_pos I).le
      (fractionalIdeal_absNorm_pos _).le]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro J
  ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

lemma summable_norm_complexFlowGaussian_ideal
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : LogCoordinates d)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements I => ‖complexFlowGaussian σ a.1.1 t u‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp_rw [enorm_complexFlowGaussian]
  rw [← normalizedTheta_fractionalIdeal_gaussian_sum σ hn I u ht]
  exact ENNReal.ofReal_ne_top

lemma summable_residueWeightedGaussian
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
      idealResidueElementWeight I hI N χ a * complexFlowGaussian σ a.1.1 t u) := by
  apply (summable_norm_complexFlowGaussian_ideal σ hn
    (integralIdealFractionalUnit I hI) u ht).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (idealResidueElementWeight_norm_le_one I hI N χ a)

 

theorem residueWeightedGaussian_ideal_units
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (u : LogCoordinates d) {t : ℝ} (ht : 0 < t) :
    (∑' a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
      idealResidueElementWeight I hI N χ a * complexFlowGaussian σ a.1.1 t u) =
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealResidueCoefficient I hI N χ J *
        ∑' z : (𝓞 K)ˣ, complexFlowGaussian σ
          ((z:K)*(idealElementRepresentative _ J).1.1) t u := by
  let F := fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
    idealResidueElementWeight I hI N χ a * complexFlowGaussian σ a.1.1 t u
  let e := idealElementDecomposition (integralIdealFractionalUnit I hI)
  have HS : Summable (fun x => F (e x)) := e.summable_iff.mpr
    (summable_residueWeightedGaussian σ hn I hI N χ u ht)
  rw [← e.tsum_eq F, HS.tsum_sigma]
  apply tsum_congr
  intro J
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  change idealResidueElementWeight I hI N χ
    (idealElementUnitAction _ z (idealElementRepresentative _ J)) * _ = _
  rw [idealResidueElementWeight_unitAction,hunit,one_mul]
  rfl

 
def integralIdealNonzeroEquiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    {a : I // a ≠ 0} ≃ nonzeroIdealElements (integralIdealFractionalUnit I hI) where
  toFun a := ⟨Units.mk0 (((a.1:I):𝓞 K):K) (by
    intro h
    apply a.2
    apply Subtype.ext
    exact NumberField.RingOfIntegers.coe_injective (by simpa using h)),
    FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.1.property⟩
  invFun a := ⟨⟨idealIntegerElement I hI a,
    ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.1⟩, by
    intro h
    have H := congrArg (fun x : I => ((x:𝓞 K):K)) h
    simp only [ZeroMemClass.coe_zero,_root_.map_zero,idealIntegerElement_coe] at H
    exact a.1.ne_zero H⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    exact idealIntegerElement_coe I hI _
  right_inv a := by
    apply Subtype.ext
    apply Units.ext
    exact idealIntegerElement_coe I hI a

lemma idealResidueFlowTheta_nonzero
    (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (u : LogCoordinates d) (t : ℝ) :
    idealResidueFlowTheta σ I N χ u t =
    ∑' a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
      idealResidueElementWeight I hI N χ a * complexFlowGaussian σ a.1.1 t u := by
  let : Nontrivial ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) :=
    mulChar_nontrivial_domain χ hχ
  rw [idealResidueFlowTheta_eq_complex]
  let F := fun a : I =>
    χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a:𝓞 K)) *
      complexFlowGaussian σ ((a:𝓞 K):K) t u
  change (∑' a, F a) = _
  have H : Function.support F ⊆ {a : I | a ≠ 0} := by
    intro a ha he
    subst a
    simp [F,Function.mem_support,MulChar.map_zero] at ha
  rw [← tsum_subtype_eq_of_support_subset H,
    ← (integralIdealNonzeroEquiv I hI).tsum_eq]
  apply tsum_congr
  intro a
  have HA : idealIntegerElement I hI ((integralIdealNonzeroEquiv I hI) a) =
      (a.1:𝓞 K) := NumberField.RingOfIntegers.coe_injective
        (idealIntegerElement_coe I hI _)
  simp only [F,idealResidueElementWeight,HA]
  rfl

 

theorem idealResidueFlowTheta_ideal_units
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (u : LogCoordinates d) {t : ℝ} (ht : 0 < t) :
    idealResidueFlowTheta σ I N χ u t =
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealResidueCoefficient I hI N χ J *
        ∑' z : (𝓞 K)ˣ, complexFlowGaussian σ
          ((z:K)*(idealElementRepresentative _ J).1.1) t u := by
  rw [idealResidueFlowTheta_nonzero σ I hI N χ hχ]
  exact residueWeightedGaussian_ideal_units σ hn I hI N χ hunit u ht

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

lemma integrable_weightedIdealUnitOrbits
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun p => ∑' J : integralIdealClassFiber I,
      w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p)
        ((volume.restrict (Ioi 0)).prod (volume.restrict D)) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have HM (J : integralIdealClassFiber I) :=
    (measurable_unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s).const_mul (w J)
  refine ⟨(Measurable.tsum HM).aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖∑' J : integralIdealClassFiber I,
    w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) < ⊤
  apply lt_of_le_of_lt (lintegral_mono (fun p => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun J => (HM J).enorm.aemeasurable)]
  exact lt_top_iff_ne_top.mpr
    (tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top σ hn I S hD w hw hs)

omit [NumberField K] [NumberField.IsTotallyReal K] in
lemma unitOrbitMellinKernel_top (σ : OrderedEmbeddings (d+1) K)
    (a : K) (s : ℂ) (p : ℝ × LogCoordinates d) :
    unitOrbitMellinKernel σ ⊤ a s p =
    (p.1:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
      ∑' z : (𝓞 K)ˣ, complexFlowGaussian σ ((z:K)*a) p.1 p.2 := by
  unfold unitOrbitMellinKernel
  congr 1
  exact (Subgroup.topEquiv : (⊤ : Subgroup (𝓞 K)ˣ) ≃* (𝓞 K)ˣ).toEquiv.tsum_eq
    (fun z => complexFlowGaussian σ ((z:K)*a) p.1 p.2)

omit [NumberField.IsTotallyReal K] in
lemma residueMellinKernel_eq_ideal_sum
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (s : ℂ) (p : ℝ × LogCoordinates d) (ht : 0 < p.1) :
    (p.1:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) * idealResidueFlowTheta σ I N χ p.2 p.1 =
      ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        idealResidueCoefficient I hI N χ J *
          unitOrbitMellinKernel σ ⊤ (idealElementRepresentative _ J).1.1 s p := by
  rw [idealResidueFlowTheta_ideal_units σ hn I hI N χ hχ hunit _ ht,← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [unitOrbitMellinKernel_top]
  ring

 

theorem idealResidueFlowTheta_mellin
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) D volume)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ∫ u in D, idealResidueFlowTheta σ I N χ u t)
      (((d+1:ℕ):ℂ)*s/2) =
      (Nat.card (subgroupUnitLogOnto σ ⊤).ker : ℂ) *
        ((2/(d+1:ℂ)) *
          ((1/2:ℂ)*(Real.pi:ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1)) *
        ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^(-s) *
          ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
            idealResidueCoefficient I hI N χ J *
              ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  let F := fun p : ℝ × LogCoordinates d =>
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealResidueCoefficient I hI N χ J *
        unitOrbitMellinKernel σ ⊤ (idealElementRepresentative _ J).1.1 s p
  have HI : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict D)) :=
    integrable_weightedIdealUnitOrbits σ hn _ ⊤ hD _
      (fun J => idealResidueElementWeight_norm_le_one I hI N χ _) hs
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ u in D, F (t,u) := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [smul_eq_mul,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      exact residueMellinKernel_eq_ideal_sum σ hn I hI N χ hχ hunit s (t,u) ht
    _ = ∫ p, F p ∂(volume.restrict (Ioi 0)).prod (volume.restrict D) :=
      (integral_prod F HI).symm
    _ = _ := integral_weightedIdealUnitOrbits σ hn _ ⊤ hD _
      (fun J => idealResidueElementWeight_norm_le_one I hI N χ _) hs

 

theorem idealResidueCompleted_entire
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (fun s =>
      mellin (fun t => ∫ u in orderedThetaLogDomain σ, idealResidueFlowTheta σ I N χ u t)
        (((d+1:ℕ):ℂ)*s/2)) := by
  exact (idealResidueFlowTheta_boundedAverage_entire σ hn I hI N hcop χ hχ
    (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)).comp
      (by fun_prop)

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

def residueIdealMellinFactor (σ : OrderedEmbeddings (d+1) K) : ℂ :=
  (Nat.card (subgroupUnitLogOnto σ ⊤).ker : ℂ) *
    (2/(d+1:ℂ)) * (1/2:ℂ)^(d+1)

lemma residueIdealMellinFactor_ne_zero (σ : OrderedEmbeddings (d+1) K) :
    residueIdealMellinFactor σ ≠ 0 := by
  have hn : (d+1:ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have hk : (Nat.card (subgroupUnitLogOnto σ ⊤).ker : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_ne_zero (mul_ne_zero hk (div_ne_zero (by norm_num) hn))
    (pow_ne_zero _ (by norm_num))

 

def residueIdealContinued (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (s : ℂ) : ℂ :=
  (residueIdealMellinFactor σ)⁻¹ * ((Complex.Gammaℝ s)⁻¹)^(d+1) *
    ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in orderedThetaLogDomain σ, idealResidueFlowTheta σ I N χ u t)
        (((d+1:ℕ):ℂ)*s/2)

 
theorem residueIdealContinued_entire
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (residueIdealContinued σ I hI N χ) := by
  apply Differentiable.mul _ (idealResidueCompleted_entire σ hn I hI N hcop χ hχ)
  apply Differentiable.mul
  · exact (Complex.differentiable_Gammaℝ_inv.pow (d+1)).const_mul _
  · exact differentiable_id.const_cpow (Or.inl
      (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'))

 

theorem residueIdealContinued_eq_series
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    residueIdealContinued σ I hI N χ s =
      ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        idealResidueCoefficient I hI N χ J *
          ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  have HG : (1/2:ℂ)*(Real.pi:ℂ)^(-(s/2))*Complex.Gamma (s/2) =
      (1/2:ℂ)*Complex.Gammaℝ s := by
    simp only [Complex.Gammaℝ_def,neg_div,mul_assoc]
  have HM : mellin
      (fun t => ∫ u in orderedThetaLogDomain σ, idealResidueFlowTheta σ I N χ u t)
        (((d+1:ℕ):ℂ)*s/2) =
      residueIdealMellinFactor σ * (Complex.Gammaℝ s)^(d+1) *
        ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^(-s) *
          ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
            idealResidueCoefficient I hI N χ J *
              ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
    rw [idealResidueFlowTheta_mellin σ hn I hI N χ hχ hunit
      (orderedThetaLogDomain_fundamental σ) hs,HG,mul_pow]
    unfold residueIdealMellinFactor
    ring
  have hc := residueIdealMellinFactor_ne_zero σ
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hi : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'
  have hp : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hi)
  rw [residueIdealContinued,HM,Complex.cpow_neg]
  field_simp
  simp only [one_div,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hg),one_mul]

end PrimeDegreePackets
end
end

end OAI
