import Mathlib
import OAI.NumberTheory.PrimePackets.ZeroReflection

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
namespace PrimeDegreePackets.HeckeMellin

lemma measurable_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ) :
    Measurable (fun p : ℝ × LogCoordinates d => radialKernel s r a p.1 p.2) := by
  unfold radialKernel
  have he := continuous_logEnergy a
  fun_prop

lemma lintegral_exp_product {E : Type*} [MeasureSpace E] [SFinite (volume : Measure E)]
    (f : ℝ × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (Real.exp p.1) * f (Real.exp p.1,p.2)) =
      ∫⁻ t in Ioi 0, ∫⁻ u, f (t,u) := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫⁻ u, f (t,u))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ] at H
  rw [H, Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro v
  simpa only using lintegral_const_mul' (ENNReal.ofReal (Real.exp v))
    (fun u : E => f (Real.exp v,u)) ENNReal.ofReal_ne_top

lemma lintegral_norm_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ) :
    (∫⁻ t in Ioi 0, ∫⁻ u, ENNReal.ofReal ‖radialKernel s r a t u‖) =
      ∫⁻ p, ENNReal.ofReal ‖logRadialKernel s r a p‖ := by
  rw [← lintegral_exp_product _ ((measurable_radialKernel s r a).norm.ennreal_ofReal)]
  apply lintegral_congr
  intro p
  rw [logRadialKernel_eq_radial, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]

 

theorem integrable_radialKernel_product {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (fun p : ℝ × LogCoordinates d => radialKernel s r a p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  refine ⟨(measurable_radialKernel s r a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [lintegral_prod _ ((measurable_radialKernel s r a).norm.ennreal_ofReal.aemeasurable),
    lintegral_norm_radialKernel]
  have HI := (integrable_logRadialKernel hs hr a ha).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at HI
  exact HI

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

 
def realRadialKernel {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ)
    (t : ℝ) (u : LogCoordinates d) : ℝ :=
  t^((d+1 : ℝ)*s/2-1) * Real.exp (-r*t*logEnergy a u)

lemma radialKernel_ofReal {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    radialKernel (s : ℂ) r a t u = (realRadialKernel s r a t u : ℂ) := by
  unfold radialKernel realRadialKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_exp]
  push_cast
  congr 2
  all_goals ring

lemma norm_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    ‖radialKernel s r a t u‖ = realRadialKernel s.re r a t u := by
  unfold radialKernel realRadialKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.one_re,
    Complex.neg_re, Complex.ofReal_re]
  push_cast
  congr 2
  all_goals ring

lemma integral_radialKernel_ofReal {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ) :
    (∫ t in Ioi 0, ∫ u, radialKernel (s : ℂ) r a t u) =
      ((∫ t in Ioi 0, ∫ u, realRadialKernel s r a t u : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp_rw [radialKernel_ofReal s r a ht, integral_complex_ofReal]

 

theorem integral_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ t in Ioi 0, ∫ u, realRadialKernel s r a t u) =
      (2/(d+1 : ℝ)) * ((1/2 : ℝ)*r^(-(s/2))*Real.Gamma (s/2))^(d+1) *
        (∏ i, |a i|)^(-s) := by
  have H := integral_radialKernel (s := (s : ℂ)) hs hr a ha
  rw [integral_radialKernel_ofReal] at H
  apply Complex.ofReal_injective
  rw [H]
  have hp : 0 ≤ ∏ i, |a i| := Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  push_cast
  rw [Complex.ofReal_cpow hr.le, Complex.ofReal_cpow hp]
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hg : Complex.Gamma ((s : ℂ)/2) = ((Real.Gamma (s/2) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using Complex.Gamma_ofReal (s/2)
  simp only [hg, Complex.ofReal_prod]

lemma logEnergy_embeddings {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (u : LogCoordinates d) :
    logEnergy (fun i => σ i a) u = ∑ i, (logFlowWeights u i*σ i a)^2 := by
  simp [logEnergy, restoredLogCoordinates_exp, mul_comm]

 

theorem arithmetic_gaussian_mellin {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)^(((d+1 : ℕ) : ℂ)*s/2-1) *
      ∫ u : LogCoordinates d,
        (Real.exp (-Real.pi*t*∑ i, (logFlowWeights u i*σ i a)^2) : ℂ)) =
      (2/(d+1 : ℂ)) *
        ((1/2 : ℂ)*(Real.pi : ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
        ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  have H := integral_radialKernel hs Real.pi_pos (fun i => σ i a)
    (fun i => (map_ne_zero (σ i)).mpr ha)
  rw [prod_abs_orderedEmbeddings σ hn] at H
  rw [← H]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  unfold radialKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  rw [logEnergy_embeddings, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

lemma measurable_realRadialKernel {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ) :
    Measurable (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2) := by
  unfold realRadialKernel
  have he := continuous_logEnergy a
  fun_prop

lemma ae_positive_first (d : ℕ) :
    ∀ᵐ p : ℝ × LogCoordinates d ∂(volume.restrict (Ioi 0)).prod volume, 0 < p.1 :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)

lemma integrable_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_radialKernel_product (s := (s : ℂ)) hs hr a ha).norm.congr
  filter_upwards [ae_positive_first d] with p hp
  exact norm_radialKernel (s : ℂ) r a hp p.2

 

theorem lintegral_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫⁻ t in Ioi 0, ∫⁻ u, ENNReal.ofReal (realRadialKernel s r a t u)) =
      ENNReal.ofReal ((2/(d+1 : ℝ)) *
        ((1/2 : ℝ)*r^(-(s/2))*Real.Gamma (s/2))^(d+1) * (∏ i, |a i|)^(-s)) := by
  have HI := integrable_realRadialKernel hs hr a ha
  have Hnn : 0 ≤ᵐ[(volume.restrict (Ioi 0)).prod volume]
      (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2) := by
    filter_upwards [ae_positive_first d] with p hp
    exact mul_nonneg (Real.rpow_nonneg hp.le _) (Real.exp_pos _).le
  rw [← lintegral_prod _ (measurable_realRadialKernel s r a).ennreal_ofReal.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal HI Hnn, integral_prod _ HI,
    integral_realRadialKernel hs hr a ha]

 
theorem arithmetic_gaussian_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u : LogCoordinates d, arithmeticFlowGaussian σ a t u) =
      ENNReal.ofReal ((2/(d+1 : ℝ)) *
        ((1/2 : ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^(d+1) *
          |(Algebra.norm ℚ a : ℝ)|^(-s)) := by
  have H := lintegral_realRadialKernel hs Real.pi_pos (fun i => σ i a)
    (fun i => (map_ne_zero (σ i)).mpr ha)
  rw [prod_abs_orderedEmbeddings σ hn] at H
  rw [← H]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [realRadialKernel, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    logEnergy_embeddings]
  rfl

end PrimeDegreePackets.HeckeMellin

open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 

lemma idealElementRepresentative_absNorm {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    |(Algebra.norm ℚ (idealElementRepresentative I J).1.1 : ℝ)| =
      (FractionalIdeal.absNorm I.val : ℝ) * (FractionalIdeal.absNorm J.1.val : ℝ) := by
  have h := congrArg Subtype.val (idealElementRepresentative_spec I J)
  change relativeElementIdeal I (idealElementRepresentative I J).1 = J.val at h
  have hm : J.val*I = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative I J).1 := by
    rw [← h]
    simp [relativeElementIdeal]
  have hn := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    (FractionalIdeal.absNorm U.val : ℝ)) hm
  simp only [Units.val_mul, map_mul, coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs] at hn
  rw [mul_comm] at hn
  exact hn.symm

lemma measurable_arithmeticFlowGaussian_joint {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) :
    Measurable (fun p : ℝ × LogCoordinates d => arithmeticFlowGaussian σ a p.1 p.2) := by
  unfold arithmeticFlowGaussian
  have HW := continuous_logFlowWeights (d := d)
  fun_prop

 
def realHeckeFactor (n : ℕ) (s : ℝ) : ℝ :=
  (2/(n : ℝ)) * ((1/2 : ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^n

lemma realHeckeFactor_nonneg (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ realHeckeFactor n s := by
  unfold realHeckeFactor
  have hG := Real.Gamma_pos_of_pos (half_pos hs)
  positivity

 

theorem fractionalIdealTheta_mellin_lintegral {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re)) =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s * (FractionalIdeal.absNorm I.val : ℝ)^(-s)) *
        ∑' J : integralIdealClassFiber I,
          ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  let H (J : integralIdealClassFiber I) (t : ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u
  have HM (J : integralIdealClassFiber I) : Measurable (H J) := by
    apply Measurable.mul (by fun_prop)
    exact (measurable_arithmeticFlowGaussian_joint σ _).lintegral_prod_right'
  have HE : (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re)) =
      ∫⁻ t in Ioi 0, 2 * ∑' J, H J t := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [fractionalIdealTheta_unit_unfolding σ hn hodd I hS ht]
    rw [mul_left_comm, ← ENNReal.tsum_mul_left]
  rw [HE, lintegral_const_mul' _ _ (by norm_num), lintegral_tsum (fun J => (HM J).aemeasurable)]
  have HJ (J : integralIdealClassFiber I) :
      (∫⁻ t in Ioi 0, H J t) =
        ENNReal.ofReal (realHeckeFactor (d+1) s * (FractionalIdeal.absNorm I.val : ℝ)^(-s)) *
          ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
    dsimp only [H]
    rw [arithmetic_gaussian_lintegral σ hn (idealElementRepresentative I J).1.ne_zero hs,
      idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le,
      ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (realHeckeFactor_nonneg _ hs)
        (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _))]
    simp [realHeckeFactor]
  simp_rw [HJ]
  rw [ENNReal.tsum_mul_left, mul_assoc]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 

theorem integralFractionalIdeals_norm_tsum {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) =
      ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  rw [tsum_integralFractionalIdeals K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J : ℝ)^(-s)))]
  simp only [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [integralIdeal_norm_tsum (fun m => ENNReal.ofReal ((m : ℝ)^(-s)))]
  have HE (m : ℕ) :
      (idealCoefficient K m : ℝ≥0∞) * ENNReal.ofReal ((m : ℝ)^(-s)) =
        ENNReal.ofReal (realDirichletTerm (idealCoefficientReal K) s m) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    simp [realDirichletTerm, idealCoefficientReal, Real.rpow_neg, div_eq_mul_inv]
  simp_rw [HE]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s)
    (idealCoefficient_real_summable K hs), ← dedekindZeta_real_eq_terms]

 
def nonnegativeIdealThetaMellin {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Set (LogCoordinates d)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
    ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates u)) t-1).re)

lemma rpow_cancel_ennreal_factor {x : ℝ} (hx : 0 < x) (s : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (T : ℝ≥0∞) :
    ENNReal.ofReal (x^s) * (2*ENNReal.ofReal (C*x^(-s))*T) = 2*ENNReal.ofReal C*T := by
  rw [ENNReal.ofReal_mul hC]
  calc
    _ = (2*ENNReal.ofReal C) * (ENNReal.ofReal (x^s)*ENNReal.ofReal (x^(-s))) * T := by ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
      ← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, mul_one]

 

theorem classTheta_mellin_lintegral {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K))
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) :
    (∑' c : ClassGroup (𝓞 K),
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn S (classRepresentative K c) s) =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s) *
        ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  simp only [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral σ hn hodd _ hS hs0]
  simp_rw [rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos _)
    s (realHeckeFactor_nonneg _ hs0)]
  rw [ENNReal.tsum_mul_left, tsum_idealClassPartition K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J.val : ℝ)^(-s))),
    integralFractionalIdeals_norm_tsum hs]

end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealClass_norm_tsum_ne_top {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    (∑' J : integralIdealClassFiber I,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) ≠ ⊤ := by
  let f : integralIdealClassFiber I → integralFractionalIdeals K := fun J => ⟨J.1,J.2.1⟩
  have hf : Function.Injective f := by
    intro J L H
    exact Subtype.ext (congrArg (fun X : integralFractionalIdeals K => X.val) H)
  have H := ENNReal.tsum_comp_le_tsum_of_injective hf (fun J : integralFractionalIdeals K =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)))
  rw [integralFractionalIdeals_norm_tsum hs] at H
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top H

lemma nonnegativeIdealThetaMellin_ne_top {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) : nonnegativeIdealThetaMellin σ hn S I s ≠ ⊤ := by
  rw [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral σ hn hodd I hS (lt_trans zero_lt_one hs)]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (idealClass_norm_tsum_ne_top I hs)

lemma normalizedTheta_sub_one_real {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    normalizedTheta B t-1 = ((normalizedTheta B t-1).re : ℂ) := by
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re]

lemma normalizedTheta_sub_one_re_nonneg {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    0 ≤ (normalizedTheta B t-1).re := by
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re]
  exact tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma norm_normalizedTheta_sub_one {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    ‖normalizedTheta B t-1‖ = (normalizedTheta B t-1).re := by
  conv_lhs => rw [normalizedTheta_sub_one_real B ht]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (normalizedTheta_sub_one_re_nonneg B ht)]

 
def idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) (p : ℝ × LogCoordinates d) : ℂ :=
  (p.1 : ℂ)^(((d+1 : ℕ) : ℂ)*s/2-1) *
    (normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates p.2)) p.1-1)

lemma measurable_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    Measurable (idealThetaMellinKernel σ hn I s) := by
  unfold idealThetaMellinKernel
  apply Measurable.mul (by fun_prop)
  apply Measurable.sub _ measurable_const
  unfold normalizedTheta latticeTheta
  apply Measurable.tsum
  intro z
  have HB : Measurable (fun p : ℝ × LogCoordinates d =>
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates p.2)) (euclideanInteger z)) :=
    (logScaledLattice_measurable_apply
    (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
    restoredLogCoordinates (fun i => (restoredLogCoordinates_continuous i).measurable)
    (euclideanInteger z)).comp (measurable_snd (α := ℝ))
  fun_prop

lemma norm_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    ‖idealThetaMellinKernel σ hn I s (t,u)‖ = t^((d+1 : ℝ)*s.re/2-1) *
      (normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re := by
  unfold idealThetaMellinKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, norm_normalizedTheta_sub_one _ ht]
  simp

lemma lintegral_norm_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) (S : Set (LogCoordinates d)) :
    (∫⁻ p, ENNReal.ofReal ‖idealThetaMellinKernel σ hn I s p‖
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict S)) =
      nonnegativeIdealThetaMellin σ hn S I s.re := by
  rw [lintegral_prod _ (measurable_idealThetaMellinKernel σ hn I s).norm.ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  simp_rw [norm_idealThetaMellinKernel σ hn I s ht,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

 

theorem integrable_idealThetaMellinKernel {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (idealThetaMellinKernel σ hn I s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict S)) := by
  refine ⟨(measurable_idealThetaMellinKernel σ hn I s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_norm_idealThetaMellinKernel]
  exact lt_top_iff_ne_top.mpr (nonnegativeIdealThetaMellin_ne_top σ hn hodd I hS hs)

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
