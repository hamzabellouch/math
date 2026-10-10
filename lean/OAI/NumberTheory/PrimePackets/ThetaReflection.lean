import Mathlib
import OAI.NumberTheory.PrimePackets.IdealThetaXi

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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 
def idealThetaXiOn {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Set (LogCoordinates d)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ u in S, thetaMellinXi (logScaledLattice
    (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
    (restoredLogCoordinates u)) (((d+1 : ℕ) : ℂ)*s/2)

lemma idealThetaXiOn_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Differentiable ℂ (idealThetaXiOn σ hn S I) := by
  exact (arithmeticFlowThetaXi_boundedAverage_entire
    (fractionalIdealFullLattice hn I) σ hn hS hbd).comp (by fun_prop)

lemma idealThetaXiOn_eq_integral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K))
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
  have HF := integrable_idealThetaMellinKernel σ hn hodd I
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

 

lemma idealThetaXiOn_eq {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {S : Set (LogCoordinates d)}
    (hS : MeasurableSet S) (hbd : Bornology.IsBounded S)
    (hfund : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : idealThetaXiOn σ hn S I = idealThetaXi σ hn I := by
  apply entire_eq_of_real_eq (idealThetaXiOn_entire σ hn hS hbd I) (idealThetaXi_entire σ hn I)
  intro r hr
  rw [idealThetaXiOn_eq_integral σ hn hodd hfund I (by simpa using hr),
    idealThetaXi_eq_integral σ hn hodd I (by simpa using hr),
    idealThetaMellinIntegral_real, idealThetaMellinIntegral_real]
  congr 3
  unfold nonnegativeIdealThetaMellin
  rw [fractionalIdealTheta_mellin_lintegral σ hn hodd I hfund (by linarith),
    fractionalIdealTheta_mellin_lintegral σ hn hodd I (orderedThetaLogDomain_fundamental σ) (by linarith)]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma traceDualIdeal_mul_inv {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : traceDualIdeal I = traceDualIdeal 1 * I⁻¹ := by
  apply Units.ext
  simpa only [traceDualIdeal, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_one] using FractionalIdeal.dual_eq_mul_inv ℤ ℚ I.val

lemma traceDualIdeal_involutive {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : traceDualIdeal (traceDualIdeal I) = I := by
  apply Units.ext
  exact FractionalIdeal.dual_dual ℤ ℚ I.val

lemma traceDualIdeal_norm_product {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) *
      (FractionalIdeal.absNorm I.val : ℝ) = 1 := by
  let M := fractionalIdealFullLattice hn I
  let N := fractionalIdealFullLattice hn (traceDualIdeal I)
  have hrow : rowLattice (embeddingMatrix N σ) =
      rowLattice (embeddingMatrix (traceDualFullLattice M hn) σ) := by
    rw [rowLattice_embeddingMatrix, rowLattice_embeddingMatrix, traceDualIdeal_carrier hn I]
  have hdet := abs_det_eq_of_rowLattice_eq _ _
    (embeddingMatrix_det_ne_zero N σ hn)
    (embeddingMatrix_det_ne_zero (traceDualFullLattice M hn) σ hn) hrow
  have H := congrArg (fun A => |Matrix.det A|) (traceDual_embeddingMatrix_mul M σ hn)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, abs_one, abs_mul] at H
  rw [← hdet, show N = fractionalIdealFullLattice hn (traceDualIdeal I) from rfl,
    show M = fractionalIdealFullLattice hn I from rfl,
    embeddingMatrix_abs_det_fractionalIdeal, embeddingMatrix_abs_det_fractionalIdeal] at H
  calc
    _ = (Real.sqrt |(NumberField.discr K : ℝ)| *
        (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ)) *
        (Real.sqrt |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ)) := by
      calc
        _ = (Real.sqrt |(NumberField.discr K : ℝ)|)^2 *
            (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) *
            (FractionalIdeal.absNorm I.val : ℝ) := by rw [Real.sq_sqrt (abs_nonneg _)]
        _ = _ := by ring
    _ = 1 := H

lemma neg_logDomain_fundamental {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) :
    IsAddFundamentalDomain (orderedLogSubgroup σ ⊤)
      (Neg.neg ⁻¹' orderedThetaLogDomain σ) volume := by
  apply (orderedThetaLogDomain_fundamental σ).preimage_of_equiv
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    (e := fun g : orderedLogSubgroup σ ⊤ => -g) (Equiv.neg _).bijective
  intro g u
  change -((-g : orderedLogSubgroup σ ⊤).val+u) = g.val+-u
  simp [add_comm]

 

theorem idealThetaXi_reflection {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
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
    _ = _ := congrFun (idealThetaXiOn_eq σ hn hodd hm hb (neg_logDomain_fundamental σ)
      (traceDualIdeal I)) (1-s)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealClassFiber_norm_tsum_congr {K : Type*} [Field K] [NumberField K]
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hIJ : ClassGroup.mk K I = ClassGroup.mk K J)
    (s : ℝ) :
    (∑' A : integralIdealClassFiber I,
      ENNReal.ofReal ((FractionalIdeal.absNorm A.val.val : ℝ)^(-s))) =
    (∑' A : integralIdealClassFiber J,
      ENNReal.ofReal ((FractionalIdeal.absNorm A.val.val : ℝ)^(-s))) := by
  let e : integralIdealClassFiber I ≃ integralIdealClassFiber J :=
    Equiv.subtypeEquivRight (fun A => by simp only [hIJ])
  exact e.tsum_eq (fun A : integralIdealClassFiber J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm A.val.val : ℝ)^(-s)))

lemma idealThetaMellin_normalized_congr {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
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
    rw [fractionalIdealTheta_mellin_lintegral σ hn hodd A
      (orderedThetaLogDomain_fundamental σ) HS,
      rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos A) s (realHeckeFactor_nonneg _ HS)]
  have H := congrArg ENNReal.toReal ((HI I).trans
    ((congrArg (fun T => 2 * ENNReal.ofReal (realHeckeFactor (d+1) s) * T)
      (idealClassFiber_norm_tsum_congr hIJ s)).trans (HI J).symm))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] using H

 

theorem idealThetaXi_normalized_congr {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
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
  rw [idealThetaXi_eq_integral σ hn hodd I (by simpa using hx),
    idealThetaXi_eq_integral σ hn hodd J (by simpa using hx),
    idealThetaMellinIntegral_real, idealThetaMellinIntegral_real,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos I).le,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos J).le]
  have H := congrArg (fun r : ℝ => (r : ℂ)) (idealThetaMellin_normalized_congr σ hn hodd hIJ hx)
  push_cast at H
  calc
    _ = ((((d+1 : ℕ) : ℂ)*x/2)*(((d+1 : ℕ) : ℂ)*x/2-((d+1 : ℕ) : ℂ)/2)) *
      (Complex.ofReal ((FractionalIdeal.absNorm I.val : ℝ)^x) *
        ((nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) I x).toReal : ℂ)) := by ring
    _ = _ := by rw [H]; ring

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma traceDual_norm_log {D x y : ℝ} (hD : 0 < D) (hx : 0 < x) (hy : 0 < y)
    (h : D*y*x=1) : Real.log y = -Real.log D-Real.log x := by
  have H := congrArg Real.log h
  rw [Real.log_mul (ne_of_gt (mul_pos hD hy)) (ne_of_gt hx),
    Real.log_mul (ne_of_gt hD) (ne_of_gt hy), Real.log_one] at H
  linarith

lemma norm_sqrt_inv_exp {D x : ℝ} (hD : 0 < D) (hx : 0 < x) :
    (((Real.sqrt D*x)⁻¹ : ℝ) : ℂ) =
      Complex.exp (-((Real.log D : ℂ)/2+(Real.log x : ℂ))) := by
  have he : -((Real.log D : ℂ)/2+(Real.log x : ℂ)) =
      ((-(Real.log D/2+Real.log x) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_exp, Complex.ofReal_inj, Real.exp_neg,
    Real.exp_add, ← Real.log_sqrt hD.le, Real.exp_log (Real.sqrt_pos.mpr hD), Real.exp_log hx]

 
lemma traceDual_functional_factor {D x y : ℝ} (hD : 0 < D) (hx : 0 < x) (hy : 0 < y)
    (h : D*y*x=1) (s : ℂ) :
    (x : ℂ)^s * (((Real.sqrt D*x)⁻¹ : ℝ) : ℂ) =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log D : ℂ)) * (y : ℂ)^(1-s) := by
  rw [norm_sqrt_inv_exp hD hx,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le,
    ← Complex.exp_add, ← Complex.exp_add, traceDual_norm_log hD hx hy h]
  push_cast
  congr 1
  ring

lemma completion_reflection_factor (D : ℝ) (s : ℂ) :
    Complex.exp (s*(Real.log D : ℂ)/2) *
      Complex.exp (((1/2 : ℂ)-s)*(Real.log D : ℂ)) =
      Complex.exp ((1-s)*(Real.log D : ℂ)/2) := by
  rw [← Complex.exp_add]
  congr 1
  ring

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXi_normalized_reflection {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ)^s * idealThetaXi σ hn I s =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        (((FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) : ℂ)^(1-s) *
          idealThetaXi σ hn (traceDualIdeal I) (1-s)) := by
  rw [idealThetaXi_reflection σ hn hodd I s, ← mul_assoc, abs_inv,
    embeddingMatrix_abs_det_fractionalIdeal]
  rw [traceDual_functional_factor (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))
    (fractionalIdeal_absNorm_pos I) (fractionalIdeal_absNorm_pos (traceDualIdeal I))
    (traceDualIdeal_norm_product σ hn I), mul_assoc]

 
def traceDualClassEquiv (K : Type*) [Field K] [NumberField K] :
    ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv _).trans (Equiv.mulLeft (ClassGroup.mk K (traceDualIdeal 1)))

lemma traceDualClassEquiv_apply {K : Type*} [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (traceDualIdeal (classRepresentative K c)) = traceDualClassEquiv K c := by
  rw [traceDualIdeal_mul_inv, map_mul, map_inv, classRepresentative_spec]
  rfl

lemma classThetaXi_reflection {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (s : ℂ) :
    classThetaXi σ hn s =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        classThetaXi σ hn (1-s) := by
  unfold classThetaXi
  trans Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
    ∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (traceDualIdeal (classRepresentative K c)).val : ℝ) : ℂ)^(1-s) *
        idealThetaXi σ hn (traceDualIdeal (classRepresentative K c)) (1-s)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => idealThetaXi_normalized_reflection σ hn hodd _ s)
  congr 1
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
        ((FractionalIdeal.absNorm (classRepresentative K (traceDualClassEquiv K c)).val : ℝ) : ℂ)^(1-s) *
          idealThetaXi σ hn (classRepresentative K (traceDualClassEquiv K c)) (1-s) := by
      apply Finset.sum_congr rfl
      intro c _
      apply idealThetaXi_normalized_congr σ hn hodd
      rw [classRepresentative_spec, traceDualClassEquiv_apply]
    _ = _ := (traceDualClassEquiv K).sum_comp (fun c : ClassGroup (𝓞 K) =>
      ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^(1-s) *
        idealThetaXi σ hn (classRepresentative K c) (1-s))

 

theorem completedThetaXi_functionalEquation {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) (s : ℂ) :
    completedThetaXi σ hn s = completedThetaXi σ hn (1-s) := by
  unfold completedThetaXi
  rw [classThetaXi_reflection σ hn hodd s]
  calc
    _ = ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
        (Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) *
          Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ))) *
        classThetaXi σ hn (1-s) := by ring
    _ = _ := by rw [completion_reflection_factor]

end PrimeDegreePackets.HeckeMellin

open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
namespace PrimeDegreePackets.HeckeMellin

lemma totallyRealCompletedXi_real (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    conj (totallyRealCompletedXi K s) = totallyRealCompletedXi K s := by
  unfold totallyRealCompletedXi completionExponential
  rw [dedekindZeta_ofReal K s]
  have hg : Complex.Gamma ((s : ℂ)/2) = (Real.Gamma (s/2) : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    push_cast
    rfl
  rw [hg]
  simp only [map_mul, map_sub, map_one, map_pow, Complex.conj_ofReal,
    ← Complex.exp_conj, map_div₀, map_natCast, map_ofNat]

lemma completedThetaXi_conj {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) (s : ℂ) :
    completedThetaXi σ hn (conj s) = conj (completedThetaXi σ hn s) := by
  have H : Differentiable ℂ (conj ∘ completedThetaXi σ hn ∘ conj) := by
    intro z
    apply differentiableAt_conj_conj_iff.mpr
    exact completedThetaXi_entire σ hn _
  have HE := entire_eq_of_real_eq H (completedThetaXi_entire σ hn) (fun r hr => by
    simp only [Function.comp_apply, Complex.conj_ofReal]
    rw [completedThetaXi_real_eq σ hn hodd hr, totallyRealCompletedXi_real])
  have HE' := congrArg conj (congrFun HE s)
  simpa using HE'

lemma completedThetaXi_one {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) :
    completedThetaXi σ hn 1 = completedXiBoundaryValue K := by
  have HL : Tendsto (fun r : ℝ => completedThetaXi σ hn r) (𝓝[>] 1)
      (𝓝 (completedThetaXi σ hn 1)) := by
    exact (completedThetaXi_entire σ hn 1).continuousAt.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (tendsto_completedXi_from_right K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (completedThetaXi_real_eq σ hn hodd hr).symm

lemma completedThetaXi_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) :
    completedThetaXi σ hn 0 = completedXiBoundaryValue K := by
  rw [completedThetaXi_functionalEquation σ hn hodd 0, sub_zero,
    completedThetaXi_one σ hn hodd]

lemma completedThetaXi_ne_zero_of_re_gt_one {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_eq σ hn hodd hs]
  exact totallyRealCompletedXi_ne_zero K hs

lemma completedThetaXi_ne_zero_of_re_neg {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) {s : ℂ} (hs : s.re < 0) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_functionalEquation σ hn hodd s]
  apply completedThetaXi_ne_zero_of_re_gt_one σ hn hodd
  simp only [Complex.sub_re, Complex.one_re]
  linarith

 

def dedekindXiZeros {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Set ℂ := {s | completedThetaXi σ hn s = 0}

lemma dedekindXiZeros_re_mem_Icc {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K))
    {s : ℂ} (hs : s ∈ dedekindXiZeros σ hn) : s.re ∈ Icc (0:ℝ) 1 := by
  constructor
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_neg σ hn hodd (lt_of_not_ge h) hs
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_gt_one σ hn hodd (lt_of_not_ge h) hs

lemma dedekindXiZeros_ne_one {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) :
    (1 : ℂ) ∉ dedekindXiZeros σ hn := by
  change completedThetaXi σ hn 1 ≠ 0
  rw [completedThetaXi_one σ hn hodd]
  exact completedXiBoundaryValue_ne_zero K

lemma dedekindXiZeros_ne_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hodd : Odd (finrank ℚ K)) :
    (0 : ℂ) ∉ dedekindXiZeros σ hn := by
  change completedThetaXi σ hn 0 ≠ 0
  rw [completedThetaXi_zero σ hn hodd]
  exact completedXiBoundaryValue_ne_zero K

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
