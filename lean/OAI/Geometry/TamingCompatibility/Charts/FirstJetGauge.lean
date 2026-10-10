import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricOperatorInner
import OAI.Geometry.TamingCompatibility.DifferentialForms.SymbolMap

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
abbrev End := W →L[ℝ] W

def adjointCLM : End (W := W) →L[ℝ] End (W := W) :=
  ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma adjointCLM_apply (A : End (W := W)) : adjointCLM A = A.adjoint := rfl

lemma fderiv_adjoint (P : V → End (W := W)) {x : V}
    (hP : DifferentiableAt ℝ P x) (v : V) :
    fderiv ℝ (fun y => (P y).adjoint) x v = (fderiv ℝ P x v).adjoint := by
  have h := (adjointCLM.hasFDerivAt.comp x hP.hasFDerivAt).fderiv
  exact congrArg (fun f : V →L[ℝ] End (W := W) => f v) h

omit [Fintype ι] in

lemma weighted_principal_jet_skew (P : ι → ι → V → End (W := W))
    (g : ι → ι → V → ℝ) (ρ : V → ℝ) (x v : V) (i j : ι)
    (hP : ∀ i j, DifferentiableAt ℝ (P i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hstar : ∀ y, (P i j y).adjoint = P j i y)
    (hscalar : ∀ y, P i j y + P j i y = (2*(ρ y*g i j y)) • ContinuousLinearMap.id ℝ W)
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : fderiv ℝ (g i j) x = 0) :
    (fderiv ℝ (P i j) x v).adjoint = - fderiv ℝ (P i j) x v := by
  have hadj : fderiv ℝ (P j i) x v = (fderiv ℝ (P i j) x v).adjoint := by
    rw [← fderiv_adjoint (P i j) (hP i j) v]
    congr 2
    funext y
    exact (hstar y).symm
  have hder := ((hρ.hasFDerivAt.mul (hg i j).hasFDerivAt).const_smul (2:ℝ)).smul_const
    (ContinuousLinearMap.id ℝ W)
  have hsum := ((hP i j).hasFDerivAt.add (hP j i).hasFDerivAt).fderiv
  have heq : (fun y => P i j y+P j i y) =
      (fun y => ((2:ℝ) • (ρ y*g i j y)) • ContinuousLinearMap.id ℝ W) := by
    funext y
    simpa only [smul_eq_mul] using hscalar y
  change fderiv ℝ (fun y => P i j y + P j i y) x = _ at hsum
  rw [heq] at hsum
  have hderEq : fderiv ℝ (fun y => ((2:ℝ) • (ρ y*g i j y)) • ContinuousLinearMap.id ℝ W) x =
      ((2:ℝ) • (ρ x • fderiv ℝ (g i j) x + g i j x • fderiv ℝ ρ x)).smulRight
        (ContinuousLinearMap.id ℝ W) := hder.fderiv
  rw [hderEq] at hsum
  have hv := congrArg (fun f : V →L[ℝ] End (W := W) => f v) hsum
  simp [hρ0, hg0] at hv
  rw [hadj] at hv
  exact eq_neg_of_add_eq_zero_right hv.symm

def squareFirst (P' : ι → ι → End (W := W)) (a : ι → W →L[ℝ] Q)
    (b : W →L[ℝ] Q) (ρ : ℝ) (j : ι) : End (W := W) :=
  -ρ⁻¹ • (∑ i, P' i j) + b.adjoint ∘L a j - (a j).adjoint ∘L b

lemma squareFirst_skew (P' : ι → ι → End (W := W)) (a : ι → W →L[ℝ] Q)
    (b : W →L[ℝ] Q) (ρ : ℝ) (j : ι)
    (hP : ∀ i, (P' i j).adjoint = - P' i j) :
    (squareFirst P' a b ρ j).adjoint = - squareFirst P' a b ρ j := by
  simp [squareFirst, map_add, map_sub, map_smul, map_sum, hP,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  abel

def halfJet (q : ι → V →L[ℝ] ℝ) (b : ι → End (W := W)) : V →L[ℝ] End (W := W) :=
  ∑ i, (q i).smulRight ((1/2:ℝ) • b i)

lemma halfJet_skew (q : ι → V →L[ℝ] ℝ) (b : ι → End (W := W))
    (hb : ∀ i, (b i).adjoint = -b i) (z : V) :
    (halfJet q b z).adjoint = - halfJet q b z := by
  simp [halfJet, map_sum, map_smul, hb, smul_neg, Finset.sum_neg_distrib]

omit [CompleteSpace W] in
lemma halfJet_direction [DecidableEq ι] (q : ι → V →L[ℝ] ℝ) (e : ι → V)
    (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0) (b : ι → End (W := W)) (j : ι) :
    halfJet q b (e j) = (1/2:ℝ) • b j := by
  simp [halfJet, hqe]

def transformedFirst (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (U : V → End (W := W)) (e : ι → V) (j : ι) (z : V) : End (W := W) :=
  (U z).adjoint ∘L ((b j z) ∘L U z -
    ∑ i, (a i j z+a j i z) • (fderiv ℝ U z (e i)))

lemma transformedFirst_contDiff (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (U : V → End (W := W)) (e : ι → V) (j : ι)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (hU : ContDiff ℝ ∞ U) : ContDiff ℝ ∞ (transformedFirst a b U e j) := by
  have hDU : ContDiff ℝ ∞ (fderiv ℝ U) := hU.fderiv_right (by simp)
  exact (adjointCLM.contDiff.comp hU).clm_comp
    (((hb j).clm_comp hU).sub (ContDiff.sum fun i _ =>
      ((ha i j).add (ha j i)).smul (hDU.clm_apply contDiff_const)))

lemma transformedFirst_zero [DecidableEq ι]
    (q : ι → V →L[ℝ] ℝ) (e : ι → V)
    (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0)
    (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (ha : ∀ i j, a i j 0 = if i=j then 1 else 0) (j : ι) :
    transformedFirst a b (OrthogonalJets.gauge (halfJet q (fun i => b i 0))) e j 0 = 0 := by
  have hd := (OrthogonalJets.gauge_hasFDerivAt_zero (halfJet q (fun i => b i 0))).fderiv
  simp only [transformedFirst, OrthogonalJets.gauge_zero, hd, halfJet_direction q e hqe]
  have he : (∑ i, (a i j 0+a j i 0) • ((1/2:ℝ) • b i 0)) = b j 0 := by
    rw [Finset.sum_eq_single j]
    · simp only [ha, ite_true, smul_smul]
      norm_num
    · intro i _ hij
      simp [ha, hij, Ne.symm hij]
    · simp
  rw [he]
  simp [ContinuousLinearMap.one_def]

end TamingCompatibility.GeometricHilbert.FirstJetGauge

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets GeometricNormalCharts CoordinateOperator HodgeNormalSymbol
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma pulled_covector (b : Fin 4 → V) (C : V →L[ℝ] V) (i : Fin 4) :
    (WithLp.toLp 2 (fun k => C (b k) i) : V) =
      (frameMap b).adjoint (C.adjoint (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]
  simp [frameMap_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

lemma pulled_principal (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (L : V ≃L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j +
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i =
      (2 * principal (MetricDensity.pullMetric g.bilinear L.toContinuousLinearMap) i j) •
        ContinuousLinearMap.id ℝ W := by
  rw [pullCoefficient_polarized,principal_pullback_frame g.bilinear (frameEquiv g b hb) L
    (frameMap_metric g b hb),pulled_covector,pulled_covector]
  rfl

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
