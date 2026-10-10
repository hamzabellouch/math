import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos2

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

lemma zeroMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : P × V => zeroMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      lowerMatrix (fun k z => a k (y.1,z)) (fun z => b (y.1,z))
        (fun z => ρ (y.1,z)) i y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp hb
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact ((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gaugeFirst_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hU : ContDiffAt ℝ ∞ U x) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeFirst e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => U (y.1,z)) j y.2) x := by
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hb j).clm_comp hU).sub (ContDiffAt.sum (fun i _ =>
      ((ha i j).add (ha j i)).smul
        ((slice_fderiv_contDiffAt U hU).clm_apply (contDiffAt_const (c := e i))))))

lemma gaugeZero_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (c U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) (hU : ContDiffAt ℝ ∞ U x) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeZero e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => c (y.1,z)) (fun z => U (y.1,z)) y.2) x := by
  have hdu (j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => U (y.1,z)) y.2 (e j)) x :=
    (slice_fderiv_contDiffAt U hU).clm_apply contDiffAt_const
  have hddu (i j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => fderiv ℝ (fun w => U (y.1,w)) z (e j)) y.2 (e i)) x :=
    (slice_fderiv_contDiffAt _ (hdu j)).clm_apply contDiffAt_const
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hc.clm_comp hU).add (ContDiffAt.sum (fun i _ => (hb i).clm_comp (hdu i)))).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (ha i j).smul (hddu i j)))

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace

def regularMetrics : Set (MetricTensor (V := V)) :=
  {M | 0 < (gram (stdOrthonormalBasis ℝ V).toBasis M).det ∧ (metricOperator M).IsInvertible}

lemma regularMetrics_open : IsOpen regularMetrics :=
  (isOpen_lt continuous_const detGram_contDiff.continuous).inter
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := V) (F := V)).preimage metricOperator.continuous)

lemma euclidean_mem_regularMetrics : EMetric ∈ regularMetrics := by
  constructor
  · simp [gram_euclidean]
  · rw [metricOperator_euclidean]
    exact ⟨ContinuousLinearEquiv.refl ℝ V,rfl⟩

lemma volumeDensity_contDiffAt_regular {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
    ContDiffAt ℝ ∞ volumeDensity M :=
  detGram_contDiff.contDiffAt.sqrt (ne_of_gt hM.1)

lemma volumeDensity_pos {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
    0 < volumeDensity M := Real.sqrt_pos.mpr hM.1

lemma principal_contDiffAt_regular {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun L => principal L i j) M :=
  ContDiffAt.inner ℝ (((hM.2.contDiffAt_map_inverse.comp M metricOperator.contDiff.contDiffAt).clm_apply
    contDiffAt_const)) contDiffAt_const

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance firstMatrixJointMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance firstMatrixJointMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ActualData.jets (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (hactual : ActualData J α ht p D q g B) :
      (∀ i, ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0) ∧
      ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 ∧
      (let m := fun z => normalMetric g B (q,z)
       let ρ := fun z => volumeDensity (m z)
       ContDiffAt ℝ ∞ ρ 0 ∧ ρ 0 = 1 ∧ fderiv ℝ ρ 0 = 0 ∧
       (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
         principal (m 0) i j = (if i=j then 1 else 0) ∧
         fderiv ℝ (fun z => principal (m z) i j) 0 = 0) ∧
       (∀ j, (actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0).adjoint =
         -actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0)) := by
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  have hq := hOD hqO
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqO]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hzero : affineMetric g B (q,0) = innerSL ℝ (E := Space) := by
    simp only [affineMetric,map_zero,add_zero,hgact q hqO,hBact q hqO]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact frameMap_metric _ _ (D.frame_gram q hq) v w
  obtain ⟨hρ,hρone,hρzero,hpr⟩ := normal_density_principal_jets g B hg hB hsym q hzero
  have ha := pulledA_contDiffAt J α ht p D g B q hq hBq
  refine ⟨ha,pulledB_contDiffAt J α hs ht p D g B q hq,hρ,hρone,hρzero,hpr,?_⟩
  intro j
  exact actualSquareFirst_skew EuclideanEnergy.e _ _ _ _ 0
    (fun i => (ha i).differentiableAt (by simp)) (hρ.differentiableAt (by simp))
    (fun i j => (hpr i j).1.differentiableAt (by simp))
    (fun i j => pulledA_weighted_principal J α ht p D g B hg hB hsym O hO hOD hgact
      q hqO hBq i j) hρzero (fun i j => (hpr i j).2.2) j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
