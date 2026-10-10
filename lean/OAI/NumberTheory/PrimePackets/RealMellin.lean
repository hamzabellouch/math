import Mathlib
import OAI.NumberTheory.PrimePackets.DiscriminantBounds
import OAI.NumberTheory.PrimePackets.ThetaReflection

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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

theorem classTheta_mellin_lintegral_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) :
    (∑' c : ClassGroup (𝓞 K),
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn S (classRepresentative K c) s) =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s) *
        ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  simp only [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  _ hS hs0]
  simp_rw [rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos _)
    s (realHeckeFactor_nonneg _ hs0)]
  rw [ENNReal.tsum_mul_left, tsum_idealClassPartition K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J.val : ℝ)^(-s))),
    integralFractionalIdeals_norm_tsum hs]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma nonnegativeIdealThetaMellin_ne_top_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) : nonnegativeIdealThetaMellin σ hn S I s ≠ ⊤ := by
  rw [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  I hS (lt_trans zero_lt_one hs)]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (idealClass_norm_tsum_ne_top I hs)

theorem integrable_idealThetaMellinKernel_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (idealThetaMellinKernel σ hn I s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict S)) := by
  refine ⟨(measurable_idealThetaMellinKernel σ hn I s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_norm_idealThetaMellinKernel]
  exact lt_top_iff_ne_top.mpr (nonnegativeIdealThetaMellin_ne_top_totallyReal σ hn  I hS hs)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXi_eq_integral_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    idealThetaXi σ hn I s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      ∫ p, idealThetaMellinKernel σ hn I s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (orderedThetaLogDomain σ)) := by
  let z : ℂ := ((d+1 : ℕ) : ℂ)*s/2
  have hzre : ((d+1 : ℕ) : ℝ)/2 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hd : (0 : ℝ) < d+1 := by positivity
    push_cast
    nlinarith
  have hz : z ≠ 0 := by
    intro H
    rw [H, Complex.zero_re] at hzre
    have : (0 : ℝ) ≤ ((d+1 : ℕ) : ℝ)/2 := by positivity
    linarith
  have hza : z ≠ ((d+1 : ℕ) : ℂ)/2 := by
    intro H
    simp only [H, Complex.div_ofNat_re, Complex.natCast_re] at hzre
    exact (lt_irrefl _ hzre)
  have HF := integrable_idealThetaMellinKernel_totallyReal σ hn  I
    (orderedThetaLogDomain_fundamental σ) hs
  rw [integral_prod_symm _ HF]
  unfold idealThetaXi
  calc
    _ = ∫ u in orderedThetaLogDomain σ,
        (z*(z-((d+1 : ℕ) : ℂ)/2))*
          ∫ t in Ioi 0, idealThetaMellinKernel σ hn I s (t,u) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only
      rw [thetaMellinXi_eq _ hz (by simpa only [Fintype.card_fin] using hza)]
      have HM := (normalizedTheta_hasMellin
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) (s := z)
        (by simpa only [Fintype.card_fin] using hzre)).2
      rw [← HM]
      simp only [Fintype.card_fin, mellin, smul_eq_mul, idealThetaMellinKernel, z]
    _ = _ := integral_const_mul _ _

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma classTheta_mellin_integral_real_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℝ} (hs : 1 < s) :
    (∑ c : ClassGroup (𝓞 K),
      (FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
        (classRepresentative K c) s).toReal) =
      2 * realHeckeFactor (d+1) s * (NumberField.dedekindZeta K s).re := by
  have H := congrArg ENNReal.toReal (classTheta_mellin_lintegral_totallyReal σ hn 
    (orderedThetaLogDomain_fundamental σ) hs)
  have HT (c : ClassGroup (𝓞 K)) :
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) (classRepresentative K c) s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (nonnegativeIdealThetaMellin_ne_top_totallyReal σ hn  _ (orderedThetaLogDomain_fundamental σ) hs)
  rw [ENNReal.tsum_toReal_eq HT] at H
  simpa only [tsum_fintype, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _), ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (realHeckeFactor_nonneg _ (lt_trans zero_lt_one hs)),
    ENNReal.toReal_ofReal (dedekindZeta_real_nonneg K s)] using H

theorem classThetaXi_real_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℝ} (hs : 1 < s) :
    classThetaXi σ hn s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      (2*realHeckeFactor (d+1) s : ℝ) * NumberField.dedekindZeta K s := by
  let A : ℂ := (((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
        A * (((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
          (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
            (classRepresentative K c) s).toReal : ℝ) : ℂ) := by
      unfold classThetaXi
      apply Finset.sum_congr rfl
      intro c _
      rw [idealThetaXi_eq_integral_totallyReal σ hn  _ (by simpa using hs),
        idealThetaMellinIntegral_real, ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le,
        Complex.ofReal_mul]
      dsimp [A]
      ring
    _ = A * (((∑ c : ClassGroup (𝓞 K),
        (FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
          (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
            (classRepresentative K c) s).toReal) : ℝ) : ℂ) := by
      rw [← Finset.mul_sum, Complex.ofReal_sum]
    _ = _ := by
      rw [classTheta_mellin_integral_real_totallyReal σ hn  hs, Complex.ofReal_mul,
        dedekindZeta_real_value]
      simp only [A, mul_assoc]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma completedThetaXi_real_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℝ} (hs : 1 < s) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  unfold completedThetaXi
  rw [classThetaXi_real_eq_totallyReal σ hn  hs, Complex.ofReal_mul, Complex.ofReal_ofNat,
    realHeckeFactor_ofReal]
  let E : ℂ := Complex.exp ((s : ℂ)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2)
  let P : ℂ := (Real.pi : ℂ)^(-(s : ℂ)/2)
  let G : ℂ := Complex.Gamma ((s : ℂ)/2)
  have H := hecke_factor_cancellation (d+1) (by omega) (s : ℂ) P G
  calc
    _ = E * (((2:ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
        ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
        (2*(2/((d+1 : ℕ) : ℂ)*((1/2:ℂ)*P*G)^(d+1)))) * NumberField.dedekindZeta K s := by
      dsimp [E,P,G]
      ring
    _ = E * ((s : ℂ)*(s-1)*P^(d+1)*G^(d+1)) * NumberField.dedekindZeta K s := by rw [H]
    _ = (s : ℂ)*(s-1)*(E*P^(d+1))*G^(d+1)*NumberField.dedekindZeta K s := by ring
    _ = _ := by
      rw [show E*P^(d+1) = completionExponential (d+1) |(NumberField.discr K : ℝ)| s from
        conductor_pi_factor _ _ _]
      simp only [totallyRealCompletedXi, hn, G]

theorem completedThetaXi_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  exact halfPlane_eq_of_real_eq (completedThetaXi_entire σ hn).differentiableOn
    (fun z hz => (totallyRealCompletedXi_differentiableAt K hz).differentiableWithinAt)
    (fun r hr => completedThetaXi_real_eq_totallyReal σ hn  hr) hs

lemma completedThetaXi_not_identically_zero_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    completedThetaXi σ hn 2 ≠ 0 := by
  rw [completedThetaXi_eq_totallyReal σ hn  (by norm_num)]
  exact totallyRealCompletedXi_ne_zero K (by norm_num)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma regularizedThetaZeta_eq_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℂ} (hs : 1 < s.re) :
    regularizedThetaZeta σ hn s = (s-1)*NumberField.dedekindZeta K s := by
  unfold regularizedThetaZeta
  rw [completedThetaXi_eq_totallyReal σ hn  hs]
  have hE := completionExponential_ne_zero (d+1) |(NumberField.discr K : ℝ)| s
  have hG := Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith : 0 < s.re))
  have hs0 := Complex.ne_zero_of_one_lt_re hs
  unfold totallyRealCompletedXi
  rw [hn]
  rw [inv_pow]
  field_simp [hE, hG, hs0]

theorem regularizedThetaZeta_one_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     :
    regularizedThetaZeta σ hn 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
  have HC := (regularizedThetaZeta_differentiableAt σ hn one_ne_zero).continuousAt
  have HL : Tendsto (fun r : ℝ => regularizedThetaZeta σ hn r) (𝓝[>] 1)
      (𝓝 (regularizedThetaZeta σ hn 1)) := by
    exact HC.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (regularizedThetaZeta_eq_totallyReal σ hn  (by simpa using hr)).symm

lemma regularizedThetaZeta_eventually_ne_zero_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     :
    ∀ᶠ s in 𝓝 (1 : ℂ), regularizedThetaZeta σ hn s ≠ 0 := by
  apply (regularizedThetaZeta_differentiableAt σ hn one_ne_zero).continuousAt.eventually_ne
  rw [regularizedThetaZeta_one_totallyReal σ hn ]
  exact Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero K)

lemma completedThetaXi_logDeriv_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedThetaXi σ hn) s = logDeriv (totallyRealCompletedXi K) s := by
  apply Filter.EventuallyEq.eq_of_nhds
  apply logDeriv_congr_nhds
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
  exact completedThetaXi_eq_totallyReal σ hn  hz

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXiOn_eq_integral_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    idealThetaXiOn σ hn S I s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      ∫ p, idealThetaMellinKernel σ hn I s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (S)) := by
  let z : ℂ := ((d+1 : ℕ) : ℂ)*s/2
  have hzre : ((d+1 : ℕ) : ℝ)/2 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hd : (0 : ℝ) < d+1 := by positivity
    push_cast
    nlinarith
  have hz : z ≠ 0 := by
    intro H
    rw [H, Complex.zero_re] at hzre
    have : (0 : ℝ) ≤ ((d+1 : ℕ) : ℝ)/2 := by positivity
    linarith
  have hza : z ≠ ((d+1 : ℕ) : ℂ)/2 := by
    intro H
    simp only [H, Complex.div_ofNat_re, Complex.natCast_re] at hzre
    exact (lt_irrefl _ hzre)
  have HF := integrable_idealThetaMellinKernel_totallyReal σ hn  I
    hS hs
  rw [integral_prod_symm _ HF]
  unfold idealThetaXiOn
  calc
    _ = ∫ u in S,
        (z*(z-((d+1 : ℕ) : ℂ)/2))*
          ∫ t in Ioi 0, idealThetaMellinKernel σ hn I s (t,u) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only
      rw [thetaMellinXi_eq _ hz (by simpa only [Fintype.card_fin] using hza)]
      have HM := (normalizedTheta_hasMellin
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) (s := z)
        (by simpa only [Fintype.card_fin] using hzre)).2
      rw [← HM]
      simp only [Fintype.card_fin, mellin, smul_eq_mul, idealThetaMellinKernel, z]
    _ = _ := integral_const_mul _ _

lemma idealThetaXiOn_eq_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {S : Set (LogCoordinates d)}
    (hS : MeasurableSet S) (hbd : Bornology.IsBounded S)
    (hfund : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : idealThetaXiOn σ hn S I = idealThetaXi σ hn I := by
  apply entire_eq_of_real_eq (idealThetaXiOn_entire σ hn hS hbd I) (idealThetaXi_entire σ hn I)
  intro r hr
  rw [idealThetaXiOn_eq_integral_totallyReal σ hn  hfund I (by simpa using hr),
    idealThetaXi_eq_integral_totallyReal σ hn  I (by simpa using hr),
    idealThetaMellinIntegral_real, idealThetaMellinIntegral_real]
  congr 3
  unfold nonnegativeIdealThetaMellin
  rw [fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  I hfund (by linarith),
    fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  I (orderedThetaLogDomain_fundamental σ) (by linarith)]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

theorem idealThetaXi_reflection_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    idealThetaXi σ hn I s =
      ((|(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det⁻¹| : ℝ) : ℂ) *
        idealThetaXi σ hn (traceDualIdeal I) (1-s) := by
  unfold idealThetaXi
  rw [arithmeticFlowThetaXi_average_reflection]
  congr 1
  have HE : ∀ u : LogCoordinates d,
      thetaMellinXi (logScaledLattice
        (fullLatticeEuclideanBasis (traceDualFullLattice (fractionalIdealFullLattice hn I) hn) σ hn)
        (restoredLogCoordinates (-u)))
        (((d+1 : ℕ) : ℂ)/2-((d+1 : ℕ) : ℂ)*s/2) =
      thetaMellinXi (logScaledLattice
        (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn (traceDualIdeal I)) σ hn)
        (restoredLogCoordinates (-u))) (((d+1 : ℕ) : ℂ)*(1-s)/2) := by
    intro u
    rw [arithmeticFlowThetaXi_carrier_congr (traceDualIdeal_carrier hn I).symm σ hn]
    congr 1
    ring
  simp_rw [HE]
  let f : LogCoordinates d → ℂ := fun u => thetaMellinXi (logScaledLattice
    (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn (traceDualIdeal I)) σ hn)
    (restoredLogCoordinates u)) (((d+1 : ℕ) : ℂ)*(1-s)/2)
  have hm : MeasurableSet (Neg.neg ⁻¹' orderedThetaLogDomain σ) :=
    (ZSpan.fundamentalDomain_measurableSet _).preimage measurable_neg
  have hb : Bornology.IsBounded (Neg.neg ⁻¹' orderedThetaLogDomain σ) := by
    rw [Set.neg_preimage]
    exact (ZSpan.fundamentalDomain_isBounded _).neg
  calc
    _ = ∫ u in Neg.neg ⁻¹' orderedThetaLogDomain σ, f u := by
      simpa [Set.preimage_preimage, Function.comp_def, f] using
        (Measure.measurePreserving_neg volume).setIntegral_preimage_emb measurableEmbedding_neg f
          (Neg.neg ⁻¹' orderedThetaLogDomain σ)
    _ = _ := congrFun (idealThetaXiOn_eq_totallyReal σ hn  hm hb (neg_logDomain_fundamental σ)
      (traceDualIdeal I)) (1-s)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaMellin_normalized_congr_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hIJ : ClassGroup.mk K I = ClassGroup.mk K J) {s : ℝ} (hs : 1 < s) :
    (FractionalIdeal.absNorm I.val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) I s).toReal =
    (FractionalIdeal.absNorm J.val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) J s).toReal := by
  have HS : 0 < s := lt_trans zero_lt_one hs
  have HI (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      ENNReal.ofReal ((FractionalIdeal.absNorm A.val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) A s =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s) *
        ∑' B : integralIdealClassFiber A,
          ENNReal.ofReal ((FractionalIdeal.absNorm B.val.val : ℝ)^(-s)) := by
    unfold nonnegativeIdealThetaMellin
    rw [fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  A
      (orderedThetaLogDomain_fundamental σ) HS,
      rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos A) s (realHeckeFactor_nonneg _ HS)]
  have H := congrArg ENNReal.toReal ((HI I).trans
    ((congrArg (fun T => 2 * ENNReal.ofReal (realHeckeFactor (d+1) s) * T)
      (idealClassFiber_norm_tsum_congr hIJ s)).trans (HI J).symm))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] using H

theorem idealThetaXi_normalized_congr_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hIJ : ClassGroup.mk K I = ClassGroup.mk K J) (s : ℂ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ)^s * idealThetaXi σ hn I s =
    ((FractionalIdeal.absNorm J.val : ℝ) : ℂ)^s * idealThetaXi σ hn J s := by
  have HD (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      Differentiable ℂ (fun z : ℂ => ((FractionalIdeal.absNorm A.val : ℝ) : ℂ)^z *
        idealThetaXi σ hn A z) := by
    exact (Differentiable.const_cpow differentiable_id (Or.inl
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (fractionalIdeal_absNorm_pos _))))).mul
        (idealThetaXi_entire σ hn A)
  apply congrFun (entire_eq_of_real_eq (HD I) (HD J) fun x hx => ?_) s
  rw [idealThetaXi_eq_integral_totallyReal σ hn  I (by simpa using hx),
    idealThetaXi_eq_integral_totallyReal σ hn  J (by simpa using hx),
    idealThetaMellinIntegral_real, idealThetaMellinIntegral_real,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos I).le,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos J).le]
  have H := congrArg (fun r : ℝ => (r : ℂ)) (idealThetaMellin_normalized_congr_totallyReal σ hn  hIJ hx)
  push_cast at H
  calc
    _ = ((((d+1 : ℕ) : ℂ)*x/2)*(((d+1 : ℕ) : ℂ)*x/2-((d+1 : ℕ) : ℂ)/2)) *
      (Complex.ofReal ((FractionalIdeal.absNorm I.val : ℝ)^x) *
        ((nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) I x).toReal : ℂ)) := by ring
    _ = _ := by rw [H]; ring

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
