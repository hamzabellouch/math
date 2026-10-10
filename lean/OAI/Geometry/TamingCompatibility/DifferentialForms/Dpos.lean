import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.InverseCutoff
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricCoefficients
import OAI.Geometry.TamingCompatibility.Functional.NormalChart
import OAI.Geometry.TamingCompatibility.DifferentialForms.ChristoffelCLM

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def dpos (F : P × V → W) (q : P × V) : V →L[ℝ] W :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ P V)

omit [FiniteDimensional ℝ V] in
lemma dpos_eq (F : P × V → W) (hF : Differentiable ℝ F) (p : P) (z : V) :
    dpos F (p,z) = fderiv ℝ (fun u => F (p,u)) z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (c := p) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  have hh := (hF (p,z)).hasFDerivAt.comp z hd
  exact hh.fderiv.symm

omit [FiniteDimensional ℝ V] in
lemma dpos_contDiff (F : P × V → W) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (dpos F) := by
  exact (hF.fderiv_right (by simp)).clm_comp contDiff_const

lemma linear_bound (F : P × V → W) (hF : ContDiff ℝ ∞ F)
    (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ 1 →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  have hpc : Continuous (dpos F) := (dpos_contDiff F hF).continuous
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) 1)).exists_bound_of_continuousOn
    hpc.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun p hp z hz => ?_⟩
  have hd (u : V) : DifferentiableAt ℝ (fun v => F (p,v)) u :=
    (hF.differentiable (by simp) (p,u)).comp u
      ((differentiableAt_const p).prodMk differentiableAt_id)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) 1) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [← dpos_eq F (hF.differentiable (by simp))]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hd u) hb
    (show (0 : V) ∈ closedBall 0 1 by simp)
    (show z ∈ closedBall 0 1 by simpa using hz)

lemma quadratic_bound (F : P × V → W) (hF : ContDiff ℝ ∞ F)
    (K : Set P) (hK : IsCompact K) (hzero : ∀ p ∈ K, dpos F (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ 1 →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 ∧ ‖dpos F (p,z)‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := linear_bound (dpos F) (dpos_contDiff F hF) K hK
  have hlin (p : P) (hp : p ∈ K) (z : V) (hz : ‖z‖ ≤ 1) :
      ‖dpos F (p,z)‖ ≤ C*‖z‖ := by simpa [hzero p hp] using hb p hp z hz
  refine ⟨C,hC,fun p hp z hz => ⟨?_,hlin p hp z hz⟩⟩
  have hd (u : V) : DifferentiableAt ℝ (fun v => F (p,v)) u :=
    (hF.differentiable (by simp) (p,u)).comp u
      ((differentiableAt_const p).prodMk differentiableAt_id)
  have hder (u : V) (hu : u ∈ closedBall (0 : V) ‖z‖) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ C*‖z‖ := by
    have hu' : ‖u‖ ≤ ‖z‖ := by simpa using hu
    rw [← dpos_eq F (hF.differentiable (by simp))]
    exact (hlin p hp u (hu'.trans hz)).trans (mul_le_mul_of_nonneg_left hu' hC)
  have hh := (convex_closedBall (0 : V) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hd u) hder
    (show (0 : V) ∈ closedBall 0 ‖z‖ by simp)
    (show z ∈ closedBall 0 ‖z‖ by simp)
  simpa [pow_two,mul_assoc] using hh

end TamingCompatibility.GeometricHilbert.UniformJets

end

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
local instance : NormedAddCommGroup (NormalJets.MetricTensor (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (NormalJets.MetricTensor (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
open ManifoldForms ManifoldHodge MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def frameMap (b : Fin 4 → Space) : Space →L[ℝ] Space :=
  ∑ i, (EuclideanSpace.proj i).smulRight (b i)

@[simp] lemma frameMap_apply (b : Fin 4 → Space) (v : Space) :
    frameMap b v = ∑ i, v i • b i := by
  simp [frameMap]

lemma frameMap_smooth {U : Set Space} (b : Fin 4 → Space → Space)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun z => frameMap (fun i => b i z)) U := by
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.smulRight (hb i)

lemma frameMap_metric (g : MetricModel.Metric Space) (b : Fin 4 → Space)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (u v : Space) :
    g.bilinear (frameMap b u) (frameMap b v) = ⟪u,v⟫ := by
  classical
  simp only [frameMap_apply,map_sum,map_smul,_root_.sum_apply,
    _root_.smul_apply,smul_eq_mul]
  simp only [hb]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

def frameEquiv (g : MetricModel.Metric Space) (b : Fin 4 → Space)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) : Space ≃L[ℝ] Space := by
  have hi : Function.Injective (frameMap b) := by
    intro u v huv
    have hz : frameMap b (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have hh := frameMap_metric g b hb (u-v) (u-v)
    rw [hz] at hh
    have : u-v = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by simpa using hh.symm)
    exact sub_eq_zero.mp this
  exact ContinuousLinearEquiv.ofBijective (frameMap b)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective (f := (frameMap b).toLinearMap)).mp hi))

lemma frameEquiv_coe (g : MetricModel.Metric Space) (b : Fin 4 → Space)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) :
    (frameEquiv g b hb).toContinuousLinearMap = frameMap b := rfl

lemma exists_metric_frame_extension (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
      (U : Set Space), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧
      IsOpen U ∧ q ∈ U ∧ U ⊆ D.domain ∧
      (∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear) ∧
      (∀ x ∈ U, B x = frameMap (fun i => D.frame i x)) ∧
      (∀ x v w, g x v w = g x w v) := by
  obtain ⟨φ,hφ,hφD,U,hU,hqU,hUD,hφone⟩ := SchwartzCutoff.exists_one_near D.domain_open hq
  let g := SchwartzCutoff.schwartz D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) (φ.smooth ⊤) hφ hφD
  let B := SchwartzCutoff.schwartz D.domain_open
    (frameMap_smooth D.frame D.frame_smooth) (φ.smooth ⊤) hφ hφD
  refine ⟨g,B,U,g.smooth ⊤,B.smooth ⊤,hU,hqU,hUD,?_,?_,?_⟩
  · intro x hx
    simp [g,SchwartzCutoff.schwartz_apply,hφone x hx]
  · intro x hx
    simp [B,SchwartzCutoff.schwartz_apply,hφone x hx]
  · intro x v w
    simp only [g,SchwartzCutoff.schwartz_apply,_root_.smul_apply,smul_eq_mul]
    rw [(coordinateMetric J α ht p x).symm]

def affineMetric (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (pz : Space × Space) : MetricTensor (V := Space) :=
  (g (pz.1+B pz.1 pz.2)).bilinearComp (B pz.1) (B pz.1)

lemma affineMetric_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (affineMetric g B) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  have hBc : ContDiff ℝ ∞ (fun pz : Space × Space => B pz.1) := hB.comp contDiff_fst
  exact ((hg.comp (contDiff_fst.add (hBc.clm_apply contDiff_snd))).clm_apply
    (hBc.clm_apply contDiff_const)).clm_apply (hBc.clm_apply contDiff_const)

lemma affineMetric_symm (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ∀ x v w, g x v w = g x w v)
    (pz : Space × Space) (v w : Space) : affineMetric g B pz v w = affineMetric g B pz w v :=
  hg _ _ _

def metricJet (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (p : Space) : MetricDerivative (V := Space) :=
  UniformJets.dpos (affineMetric g B) (p,0)

lemma metricJet_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (metricJet g B) :=
  (UniformJets.dpos_contDiff _ (affineMetric_contDiff g B hg hB)).comp
    (contDiff_id.prodMk contDiff_const)

lemma metricJet_eq (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (p : Space) :
    metricJet g B p = fderiv ℝ (fun z => affineMetric g B (p,z)) 0 :=
  UniformJets.dpos_eq _ ((affineMetric_contDiff g B hg hB).differentiable (by simp)) p 0

def normalMetric (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (pz : Space × Space) : MetricTensor (V := Space) :=
  pullbackMetric (fun z => affineMetric g B (pz.1,z)) (metricJet g B pz.1) pz.2

lemma normalMetric_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (normalMetric g B) := by
  have hG : ContDiff ℝ ∞ (metricJet g B) := metricJet_contDiff g B hg hB
  have hJ : ContDiff ℝ ∞ (fun pz : Space × Space =>
      normalJacobian (metricJet g B pz.1) pz.2) :=
    contDiff_const.sub (((christoffel_contDiff.comp hG).comp contDiff_fst).clm_apply contDiff_snd)
  have hM : ContDiff ℝ ∞ (fun pz : Space × Space =>
      affineMetric g B (pz.1, coordinateJet (metricJet g B pz.1) pz.2)) :=
    (affineMetric_contDiff g B hg hB).comp
      (contDiff_fst.prodMk (jointJet_contDiff _ hG))
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  change ContDiff ℝ ∞ (fun pz : Space × Space =>
    affineMetric g B (pz.1, coordinateJet (metricJet g B pz.1) pz.2)
      (normalJacobian (metricJet g B pz.1) pz.2 v)
      (normalJacobian (metricJet g B pz.1) pz.2 w))
  exact (hM.clm_apply (hJ.clm_apply contDiff_const)).clm_apply (hJ.clm_apply contDiff_const)

lemma normalMetric_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (p : Space) :
    normalMetric g B (p,0) = (g p).bilinearComp (B p) (B p) := by
  simp [normalMetric,affineMetric]

lemma normalMetric_dpos_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
    (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
    UniformJets.dpos (normalMetric g B) (p,0) = 0 := by
  rw [UniformJets.dpos_eq _ ((normalMetric_contDiff g B hg hB).differentiable (by simp))]
  have hM : ContDiff ℝ ∞ (fun z => affineMetric g B (p,z)) :=
    (affineMetric_contDiff g B hg hB).comp (contDiff_const.prodMk contDiff_id)
  have hder : HasFDerivAt (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 := by
    rw [metricJet_eq g B hg hB]
    exact (hM.differentiable (by simp) 0).hasFDerivAt
  apply pullbackMetric_fderiv_zero _ _ hM.contDiffAt hder hzero
  exact metricDerivative_symmetric _ _ hder (fun z => affineMetric_symm g B hsym (p,z))

lemma centeredDisplacement_hasFDerivAt (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    HasFDerivAt (fun u => p+B p (coordinateJet (metricJet g B p) u))
      ((B p).comp (normalJacobian (metricJet g B p) z)) z := by
  have hM : ContDiff ℝ ∞ (fun z => affineMetric g B (p,z)) :=
    (affineMetric_contDiff g B hg hB).comp (contDiff_const.prodMk contDiff_id)
  have hder : HasFDerivAt (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 := by
    rw [metricJet_eq g B hg hB]
    exact (hM.differentiable (by simp) 0).hasFDerivAt
  have hG := metricDerivative_symmetric _ _ hder (fun z => affineMetric_symm g B hsym (p,z))
  exact ((B p).hasFDerivAt.comp z (coordinateJet_hasFDerivAt_normal _ hG z)).const_add p

lemma normalMetric_eq_pullback (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    normalMetric g B (p,z) =
      (g (p+B p (coordinateJet (metricJet g B p) z))).bilinearComp
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z)
        (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z) := by
  rw [(centeredDisplacement_hasFDerivAt g B hg hB hsym p z).fderiv]
  ext v w
  rfl

lemma exists_geometric_normal_metric (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
      (U : Set Space), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧
      IsOpen U ∧ q ∈ U ∧ U ⊆ D.domain ∧
      (∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear) ∧
      (∀ x ∈ U, B x = frameMap (fun i => D.frame i x)) ∧
      (∀ x v w, g x v w = g x w v) ∧
      (∀ x ∈ U, ∃ Bx : Space ≃L[ℝ] Space, B x = Bx) ∧
      (∀ x ∈ U, normalMetric g B (x,0) = innerSL ℝ (E := Space)) ∧
      (∀ K : Set Space, IsCompact K → K ⊆ U →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ z : Space, ‖z‖ ≤ 1 →
          ‖normalMetric g B (x,z) - normalMetric g B (x,0)‖ ≤ C*‖z‖^2 ∧
          ‖UniformJets.dpos (normalMetric g B) (x,z)‖ ≤ C*‖z‖) := by
  obtain ⟨g,B,U,hg,hB,hU,hqU,hUD,hgact,hBact,hsym⟩ :=
    exists_metric_frame_extension J α hs ht p D hq
  have hzero (x : Space) (hx : x ∈ U) : affineMetric g B (x,0) = innerSL ℝ (E := Space) := by
    ext v w
    simp only [affineMetric,map_zero,add_zero,ContinuousLinearMap.bilinearComp_apply]
    rw [hgact x hx,hBact x hx]
    exact frameMap_metric _ _ (D.frame_gram x (hUD hx)) v w
  have hnzero (x : Space) (hx : x ∈ U) : normalMetric g B (x,0) = innerSL ℝ (E := Space) := by
    change pullbackMetric (fun z => affineMetric g B (x,z)) (metricJet g B x) 0 = _
    rw [pullbackMetric_zero]
    exact hzero x hx
  refine ⟨g,B,U,hg,hB,hU,hqU,hUD,hgact,hBact,hsym,?_,hnzero,?_⟩
  · intro x hx
    refine ⟨frameEquiv _ _ (D.frame_gram x (hUD hx)),?_⟩
    rw [frameEquiv_coe]
    exact hBact x hx
  · intro K hK hKU
    obtain ⟨C,hC,hb⟩ := UniformJets.quadratic_bound (normalMetric g B)
      (normalMetric_contDiff g B hg hB) K hK
      (fun x hx => normalMetric_dpos_zero g B hg hB hsym x (hzero x (hKU hx)))
    refine ⟨C,hC,fun x hx z hz => ?_⟩
    exact hb x hx z hz

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

noncomputable section

end
end
end
end
end
end
end

end OAI
