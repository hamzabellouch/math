import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.NormalDensityJacobian
import OAI.Geometry.TamingCompatibility.Elliptic.WeightedPrincipal

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

def normalMap (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q z : Space) : Space :=
  q + B q (coordinateJet (metricJet g B q) z)
def normalDifferential (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q z : Space) : Space →L[ℝ] Space :=
  (B q).comp (normalJacobian (metricJet g B q) z)

@[simp] lemma normalMap_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : normalMap g B q 0 = q := by
  simp [normalMap]
@[simp] lemma normalDifferential_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : normalDifferential g B q 0 = B q := by
  simp [normalDifferential]
lemma normalMap_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalMap g B q) :=
  contDiff_const.add ((B q).contDiff.comp (coordinateJet_contDiff _))
lemma normalDifferential_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : ContDiff ℝ ∞ (normalDifferential g B q) :=
  contDiff_const.clm_comp (normalJacobian_contDiff _)
lemma normalMap_fderiv (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (q z : Space) :
    fderiv ℝ (normalMap g B q) z = normalDifferential g B q z :=
  (centeredDisplacement_hasFDerivAt g B hg hB hsym q z).fderiv

lemma normalDifferential_eventually_invertible (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hBq : (B q).IsInvertible) :
    ∀ᶠ z in 𝓝 0, (normalDifferential g B q z).IsInvertible := by
  have hmem : B q ∈ Set.range (fun e : Space ≃L[ℝ] Space => e.toContinuousLinearMap) := hBq
  have he := (normalDifferential_contDiff g B q).continuous.continuousAt (x := (0 : Space))
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Space) (F := Space)).mem_nhds
      (by simpa using hmem))
  exact he

lemma normalInverse_contDiffAt (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hBq : (B q).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => (normalDifferential g B q z).inverse) 0 := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (normalDifferential g B q 0) := by
    rw [normalDifferential_zero]
    exact hBq.contDiffAt_map_inverse
  exact hi.comp 0 (normalDifferential_contDiff g B q).contDiffAt

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def pulledA (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (i : Fin 4) (z : Space) : W →L[ℝ] Q :=
  pullCoefficient (fun k => HodgeChart.normalA J α ht p D k (normalMap g B q z))
    (normalDifferential g B q z).inverse i

def pulledB (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q z : Space) : W →L[ℝ] Q := HodgeChart.normalB J α ht p D (normalMap g B q z)

lemma pulledA_contDiffAt (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (hq : q ∈ D.domain) (hBq : (B q).IsInvertible) (i : Fin 4) :
    ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0 := by
  change ContDiffAt ℝ ∞ (fun z => ∑ k,
    ((normalDifferential g B q z).inverse (EuclideanEnergy.e k) i) •
      HodgeChart.normalA J α ht p D k (normalMap g B q z)) 0
  apply ContDiffAt.sum
  intro k _
  have ha : ContDiffAt ℝ ∞ (HodgeChart.normalA J α ht p D k) (normalMap g B q 0) := by
    rw [normalMap_zero]
    exact (HodgeChart.normalA_smooth J α ht p D k).contDiffAt (D.domain_open.mem_nhds hq)
  exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp 0
    ((normalInverse_contDiffAt g B q hBq).clm_apply contDiffAt_const)).smul
      (ha.comp 0 (normalMap_contDiff g B q).contDiffAt)

lemma pulledB_contDiffAt (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (hq : q ∈ D.domain) :
    ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 := by
  have hb : ContDiffAt ℝ ∞ (HodgeChart.normalB J α ht p D) (normalMap g B q 0) := by
    rw [normalMap_zero]
    exact (HodgeChart.normalB_smooth J α hs ht p D).contDiffAt (D.domain_open.mem_nhds hq)
  exact hb.comp 0 (normalMap_contDiff g B q).contDiffAt

lemma pulledA_weighted_principal (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v)
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (hgact : ∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear)
    (q : Space) (hq : q ∈ U) (hBq : (B q).IsInvertible) (i j : Fin 4) :
    let ρ := fun z => volumeDensity (normalMetric g B (q,z))
    let a := pulledA J α ht p D g B q
    (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z) =ᶠ[𝓝 0]
      (fun z => (2*(ρ z*principal (normalMetric g B (q,z)) i j)) •
        ContinuousLinearMap.id ℝ W) := by
  dsimp only
  have hmap : ∀ᶠ z in 𝓝 0, normalMap g B q z ∈ U :=
    (normalMap_contDiff g B q).continuous.continuousAt
      (by simpa using hU.mem_nhds hq)
  filter_upwards [hmap,normalDifferential_eventually_invertible g B q hBq] with z hz hL
  obtain ⟨L,hL⟩ := hL
  have hg' : normalMetric g B (q,z) =
      MetricDensity.pullMetric (coordinateMetric J α ht p (normalMap g B q z)).bilinear
        L.toContinuousLinearMap := by
    rw [normalMetric_eq_pullback g B hg hB hsym]
    change MetricDensity.pullMetric (g (normalMap g B q z))
      (fderiv ℝ (normalMap g B q) z) = _
    rw [normalMap_fderiv g B hg hB hsym, ←hL, hgact _ hz]
  have hp := pulled_principal (coordinateMetric J α ht p (normalMap g B q z))
    (fun k => D.frame k (normalMap g B q z))
    (D.frame_gram _ (hUD hz)) L i j
  simp only [weightedPrincipal, map_smul, ContinuousLinearMap.smul_comp]
  rw [←smul_add]
  have ha (k : Fin 4) : pulledA J α ht p D g B q k z =
      pullCoefficient (HodgeFrozenEnergy.coefficient (fun l => D.frame l (normalMap g B q z)))
        L.symm.toContinuousLinearMap k := by
    simp only [pulledA,←hL,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [ha i,ha j,hp,smul_smul,hg']
  congr 1
  ring

def ActualData (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (q : Space)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space) : Prop :=
  ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ D.domain ∧
    (∀ y ∈ O, g y = (coordinateMetric J α ht p y).bilinear) ∧
    (∀ y ∈ O, B y = frameMap (fun i => D.frame i y)) ∧
    (∀ y v w, g y v w = g y w v)

lemma exists_actual_normal_jets (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧ ActualData J α ht p D q g B ∧
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
  obtain ⟨g,B,U,hg,hB,hU,hqU,hUD,hgact,hBact,hsym⟩ :=
    exists_metric_frame_extension J α hs ht p D hq
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqU]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hzero : affineMetric g B (q,0) = innerSL ℝ (E := Space) := by
    simp only [affineMetric,map_zero,add_zero,hgact q hqU,hBact q hqU]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact frameMap_metric _ _ (D.frame_gram q hq) v w
  obtain ⟨hρ,hρone,hρzero,hpr⟩ := normal_density_principal_jets g B hg hB hsym q hzero
  have ha := pulledA_contDiffAt J α ht p D g B q hq hBq
  refine ⟨g,B,hg,hB,⟨U,hU,hqU,hUD,hgact,hBact,hsym⟩,ha,pulledB_contDiffAt J α hs ht p D g B q hq,
    hρ,hρone,hρzero,hpr,?_⟩
  intro j
  exact actualSquareFirst_skew EuclideanEnergy.e _ _ _ _ 0
    (fun i => (ha i).differentiableAt (by simp)) (hρ.differentiableAt (by simp))
    (fun i j => (hpr i j).1.differentiableAt (by simp))
    (fun i j => pulledA_weighted_principal J α ht p D g B hg hB hsym U hU hUD hgact
      q hqU hBq i j) hρzero (fun i j => (hpr i j).2.2) j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
