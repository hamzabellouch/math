import Mathlib
import OAI.NumberTheory.PrimePackets.RadialIntegrals

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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 
def idealThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ u in orderedThetaLogDomain σ,
    thetaMellinXi (logScaledLattice
      (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
      (restoredLogCoordinates u)) (((d+1 : ℕ) : ℂ)*s/2)

lemma idealThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (idealThetaXi σ hn I) := by
  exact (arithmeticFlowThetaXi_unitAverage_entire
    (fractionalIdealFullLattice hn I) σ hn).comp (by fun_prop)

lemma idealThetaXi_eq_integral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K))
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
  have HF := integrable_idealThetaMellinKernel σ hn hodd I
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

lemma idealThetaMellinKernel_real {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    idealThetaMellinKernel σ hn I s (t,u) =
      (‖idealThetaMellinKernel σ hn I s (t,u)‖ : ℂ) := by
  rw [norm_idealThetaMellinKernel σ hn I s ht]
  simp only [Complex.ofReal_re]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  unfold idealThetaMellinKernel
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat,
    Nat.cast_add, Nat.cast_one]
  rw [normalizedTheta_sub_one_real _ ht]
  simp only [Complex.ofReal_re]

 

lemma idealThetaMellinIntegral_real {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (S : Set (LogCoordinates d)) (s : ℝ) :
    (∫ p, idealThetaMellinKernel σ hn I s p
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict S)) =
      ((nonnegativeIdealThetaMellin σ hn S I s).toReal : ℂ) := by
  calc
    _ = ∫ p, (‖idealThetaMellinKernel σ hn I s p‖ : ℂ)
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict S) := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem measurableSet_Ioi)] with p hp
      exact idealThetaMellinKernel_real σ hn I s hp p.2
    _ = ((∫ p, ‖idealThetaMellinKernel σ hn I s p‖
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict S) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (measurable_idealThetaMellinKernel σ hn I s).norm.aestronglyMeasurable,
        lintegral_norm_idealThetaMellinKernel]
      rfl

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma classTheta_mellin_integral_real {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {s : ℝ} (hs : 1 < s) :
    (∑ c : ClassGroup (𝓞 K),
      (FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
        (classRepresentative K c) s).toReal) =
      2 * realHeckeFactor (d+1) s * (NumberField.dedekindZeta K s).re := by
  have H := congrArg ENNReal.toReal (classTheta_mellin_lintegral σ hn hodd
    (orderedThetaLogDomain_fundamental σ) hs)
  have HT (c : ClassGroup (𝓞 K)) :
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) (classRepresentative K c) s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (nonnegativeIdealThetaMellin_ne_top σ hn hodd _ (orderedThetaLogDomain_fundamental σ) hs)
  rw [ENNReal.tsum_toReal_eq HT] at H
  simpa only [tsum_fintype, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _), ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (realHeckeFactor_nonneg _ (lt_trans zero_lt_one hs)),
    ENNReal.toReal_ofReal (dedekindZeta_real_nonneg K s)] using H

 
def classThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^s *
      idealThetaXi σ hn (classRepresentative K c) s

lemma classThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (classThetaXi σ hn) := by
  unfold classThetaXi
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.mul _ (idealThetaXi_entire σ hn _)
  apply Differentiable.const_cpow differentiable_id
  exact Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (fractionalIdeal_absNorm_pos _)))

lemma dedekindZeta_real_value (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    ((NumberField.dedekindZeta K s).re : ℂ) = NumberField.dedekindZeta K s := by
  rw [← idealDirichlet_eq_dedekindZeta K s]
  simp

 

theorem classThetaXi_real_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) {s : ℝ} (hs : 1 < s) :
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
      rw [idealThetaXi_eq_integral σ hn hodd _ (by simpa using hs),
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
      rw [classTheta_mellin_integral_real σ hn hodd hs, Complex.ofReal_mul,
        dedekindZeta_real_value]
      simp only [A, mul_assoc]

end PrimeDegreePackets.HeckeMellin

open Set
namespace PrimeDegreePackets.HeckeMellin

lemma hecke_factor_cancellation (n : ℕ) (hn : n ≠ 0) (s p g : ℂ) :
    ((2:ℂ)^n/n) * ((n*s/2)*(n*s/2-n/2)) *
      (2*(2/n*((1/2:ℂ)*p*g)^n)) = s*(s-1)*p^n*g^n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h2n : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_pow, mul_pow, div_pow, one_pow]
  field_simp

 

lemma halfPlane_eq_of_real_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | 1 < s.re})
    (hg : DifferentiableOn ℂ g {s | 1 < s.re})
    (hreal : ∀ s : ℝ, 1 < s → f s = g s) :
    EqOn f g {s | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 1 < s.re} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have him : Complex.ofReal '' Ioi (2 : ℝ) ⊆ {s : ℂ | f s = g s} \ {(2 : ℂ)} := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : (2 : ℝ) < x := hx
    refine ⟨hreal x (lt_trans (by norm_num) hx'), ?_⟩
    simp only [mem_singleton_iff]
    intro H
    have HR := congrArg Complex.re H
    norm_num at HR
    linarith
  have hcl : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) := by
    have H : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by simp [closure_Ioi]
    simpa only [Complex.ofReal_ofNat] using mem_closure_image Complex.continuous_ofReal.continuousAt H
  exact (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd hopen) hconn (by norm_num) (closure_mono him hcl)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma realHeckeFactor_ofReal (n : ℕ) (s : ℝ) :
    (realHeckeFactor n s : ℂ) =
      (2/(n : ℂ))*((1/2 : ℂ)*(Real.pi : ℂ)^(-(s : ℂ)/2)*Complex.Gamma (s/2))^n := by
  unfold realHeckeFactor
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_cpow Real.pi_pos.le, ← Complex.Gamma_ofReal]
  push_cast
  simp only [neg_div]

lemma conductor_pi_factor (n : ℕ) (D : ℝ) (s : ℂ) :
    Complex.exp (s*(Real.log D : ℂ)/2) * ((Real.pi : ℂ)^(-s/2))^n =
      completionExponential n D s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le, ← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold completionExponential
  congr 1
  ring

 

def completedThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
    Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) * classThetaXi σ hn s

lemma completedThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (completedThetaXi σ hn) := by
  unfold completedThetaXi
  exact (Differentiable.const_mul (by fun_prop) _).mul (classThetaXi_entire σ hn)

lemma completedThetaXi_real_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) {s : ℝ} (hs : 1 < s) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  unfold completedThetaXi
  rw [classThetaXi_real_eq σ hn hodd hs, Complex.ofReal_mul, Complex.ofReal_ofNat,
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

 

theorem completedThetaXi_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  exact halfPlane_eq_of_real_eq (completedThetaXi_entire σ hn).differentiableOn
    (fun z hz => (totallyRealCompletedXi_differentiableAt K hz).differentiableWithinAt)
    (fun r hr => completedThetaXi_real_eq σ hn hodd hr) hs

lemma completedThetaXi_not_identically_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) :
    completedThetaXi σ hn 2 ≠ 0 := by
  rw [completedThetaXi_eq σ hn hodd (by norm_num)]
  exact totallyRealCompletedXi_ne_zero K (by norm_num)

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory
open scoped Topology NumberField
namespace PrimeDegreePackets.HeckeMellin

 

def regularizedThetaZeta {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  completedThetaXi σ hn s *
    (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    ((Complex.Gamma (s/2))⁻¹)^(d+1) / s

lemma regularizedThetaZeta_differentiableAt {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {s : ℂ} (hs : s ≠ 0) : DifferentiableAt ℂ (regularizedThetaZeta σ hn) s := by
  unfold regularizedThetaZeta
  apply DifferentiableAt.div _ differentiableAt_id hs
  apply DifferentiableAt.mul
  · exact ((completedThetaXi_entire σ hn) s).mul
      ((completionExponential_hasDerivAt _ _ _).differentiableAt.inv
        (completionExponential_ne_zero _ _ _))
  · exact ((Complex.differentiable_one_div_Gamma.comp
      (differentiable_id.div_const 2)) s).pow _

lemma regularizedThetaZeta_eq {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {s : ℂ} (hs : 1 < s.re) :
    regularizedThetaZeta σ hn s = (s-1)*NumberField.dedekindZeta K s := by
  unfold regularizedThetaZeta
  rw [completedThetaXi_eq σ hn hodd hs]
  have hE := completionExponential_ne_zero (d+1) |(NumberField.discr K : ℝ)| s
  have hG := Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith : 0 < s.re))
  have hs0 := Complex.ne_zero_of_one_lt_re hs
  unfold totallyRealCompletedXi
  rw [hn]
  rw [inv_pow]
  field_simp [hE, hG, hs0]

 

theorem regularizedThetaZeta_one {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) :
    regularizedThetaZeta σ hn 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
  have HC := (regularizedThetaZeta_differentiableAt σ hn one_ne_zero).continuousAt
  have HL : Tendsto (fun r : ℝ => regularizedThetaZeta σ hn r) (𝓝[>] 1)
      (𝓝 (regularizedThetaZeta σ hn 1)) := by
    exact HC.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (regularizedThetaZeta_eq σ hn hodd (by simpa using hr)).symm

lemma regularizedThetaZeta_eventually_ne_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) :
    ∀ᶠ s in 𝓝 (1 : ℂ), regularizedThetaZeta σ hn s ≠ 0 := by
  apply (regularizedThetaZeta_differentiableAt σ hn one_ne_zero).continuousAt.eventually_ne
  rw [regularizedThetaZeta_one σ hn hodd]
  exact Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero K)

 

lemma completedThetaXi_logDeriv {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedThetaXi σ hn) s = logDeriv (totallyRealCompletedXi K) s := by
  apply Filter.EventuallyEq.eq_of_nhds
  apply logDeriv_congr_nhds
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
  exact completedThetaXi_eq σ hn hodd hz

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma entire_eq_of_real_eq {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hreal : ∀ s : ℝ, 1 < s → f s = g s) : f = g := by
  have HH := halfPlane_eq_of_real_eq hf.differentiableOn hg.differentiableOn hreal
  apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (2 : ℂ).re by norm_num)] with s hs
  exact HH hs

lemma arithmeticFlowTheta_eq_sum {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (u : LogCoordinates d) (t : ℝ) :
    normalizedTheta (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) t =
      ∑' a : M.carrier, Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
        ((∑ i, (logFlowWeights u i*σ i (a:K))^2 : ℝ) : ℂ)) := by
  unfold normalizedTheta latticeTheta
  simp_rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq, arithmeticFlowTheta_vector]
  exact M.basis.equivFun.symm.toEquiv.tsum_eq (fun a : M.carrier =>
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ((∑ i, (logFlowWeights u i*σ i (a:K))^2 : ℝ) : ℂ)))

lemma arithmeticFlowTheta_carrier_congr {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice (d+1) K} (hMN : M.carrier = N.carrier)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (u : LogCoordinates d) (t : ℝ) :
    normalizedTheta (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) t =
    normalizedTheta (logScaledLattice (fullLatticeEuclideanBasis N σ hn)
      (restoredLogCoordinates u)) t := by
  rw [arithmeticFlowTheta_eq_sum, arithmeticFlowTheta_eq_sum]
  let e : M.carrier ≃ N.carrier := Set.equivOfEq (congrArg (fun P : Submodule ℤ K => (P : Set K)) hMN)
  exact e.tsum_eq (fun a : N.carrier => Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
    ((∑ i, (logFlowWeights u i*σ i (a:K))^2 : ℝ) : ℂ)))

lemma thetaMellinXi_congr_of_normalizedTheta {ι : Type*} [Fintype ι]
    (B C : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hBC : ∀ t : ℝ, normalizedTheta B t = normalizedTheta C t) :
    thetaMellinXi B = thetaMellinXi C := by
  have H : ∀ s : ℂ, (Fintype.card ι : ℝ)/2 < s.re → thetaMellinXi B s = thetaMellinXi C s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro he
      simp only [he, Complex.zero_re] at hs
      have : (0 : ℝ) ≤ (Fintype.card ι : ℝ)/2 := by positivity
      linarith
    have hsa : s ≠ (Fintype.card ι : ℂ)/2 := by
      intro he
      simp [he] at hs
    rw [thetaMellinXi_eq B hs0 hsa, thetaMellinXi_eq C hs0 hsa,
      ← (normalizedTheta_hasMellin B hs).2, ← (normalizedTheta_hasMellin C hs).2]
    simp_rw [hBC]
  apply ((thetaMellinXi_differentiable B).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    ((thetaMellinXi_differentiable C).differentiableOn.analyticOnNhd isOpen_univ)
    (z₀ := (Fintype.card ι : ℂ)/2+1)
  have hx : (Fintype.card ι : ℝ)/2 < ((Fintype.card ι : ℂ)/2+1).re := by simp
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with s hs
  exact H s hs

lemma arithmeticFlowThetaXi_carrier_congr {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice (d+1) K} (hMN : M.carrier = N.carrier)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (u : LogCoordinates d) (s : ℂ) :
    thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) s =
    thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis N σ hn)
      (restoredLogCoordinates u)) s := by
  exact congrFun (thetaMellinXi_congr_of_normalizedTheta _ _
    (arithmeticFlowTheta_carrier_congr hMN σ hn u)) s

 
def traceDualIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ I.val) (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

lemma traceDualIdeal_carrier {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (fractionalIdealFullLattice hn (traceDualIdeal I)).carrier =
      (traceDualFullLattice (fractionalIdealFullLattice hn I) hn).carrier := by
  rw [traceDualFullLattice_carrier]
  change (FractionalIdeal.dual ℤ ℚ I.val : Submodule (𝓞 K) K).restrictScalars ℤ = _
  rw [FractionalIdeal.coe_dual ℤ ℚ I.ne_zero]
  rfl

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
