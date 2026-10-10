import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalMap

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

section FiniteDimensionalDirections
open Set Metric Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in
lemma dpos_eq_at (F : P × V → W) (p : P) (z : V) (hF : DifferentiableAt ℝ F (p,z)) :
    dpos F (p,z) = fderiv ℝ (fun u => F (p,u)) z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (c := p) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  exact (hF.hasFDerivAt.comp z hd).fderiv.symm

omit [FiniteDimensional ℝ V] in
lemma dpos_contDiffAt (F : P × V → W) (x : P × V) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (dpos F) x :=
  (hF.fderiv_right (by simp)).clm_comp contDiffAt_const

omit [FiniteDimensional ℝ V] [NormedSpace ℝ P] [NormedSpace ℝ V] in
lemma compact_tube (K : Set P) (hK : IsCompact K) (O : Set (P × V)) (hO : IsOpen O)
    (hKO : K ×ˢ {(0 : V)} ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O := by
  obtain ⟨r,hr,hsub⟩ := (hK.prod isCompact_singleton).exists_cthickening_subset_open hO hKO
  refine ⟨r,hr,?_⟩
  rintro ⟨p,z⟩ ⟨hp,hz⟩
  apply hsub
  apply mem_cthickening_of_dist_le (p,z) (p,0) r (K ×ˢ {(0 : V)}) ⟨hp,rfl⟩
  simpa [Prod.dist_eq] using hz

lemma local_linear_bound (F : P × V → W) (K : Set P) (hK : IsCompact K)
    (O : Set (P × V)) (hO : IsOpen O) (hKO : K ×ˢ {(0 : V)} ⊆ O)
    (hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O ∧
      ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r → ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  obtain ⟨r,hr,hsub⟩ := compact_tube K hK O hO hKO
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x (hsub hx))).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,r,hr,hsub,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) (hsub ⟨hp,hu⟩)).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [← dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr.le)
    (show z ∈ closedBall 0 r by simpa using hz)

lemma local_quadratic_bound (F : P × V → W) (K : Set P) (hK : IsCompact K)
    (O : Set (P × V)) (hO : IsOpen O) (hKO : K ×ˢ {(0 : V)} ⊆ O)
    (hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x) (hzero : ∀ p ∈ K, dpos F (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O ∧
      ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
        ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 ∧ ‖dpos F (p,z)‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,r,hr,hsub,hb⟩ := local_linear_bound (dpos F) K hK O hO hKO
    (fun x hx => dpos_contDiffAt F x (hF x hx))
  have hlin (p : P) (hp : p ∈ K) (z : V) (hz : ‖z‖ ≤ r) :
      ‖dpos F (p,z)‖ ≤ C*‖z‖ := by simpa [hzero p hp] using hb p hp z hz
  refine ⟨C,hC,r,hr,hsub,fun p hp z hz => ⟨?_,hlin p hp z hz⟩⟩
  have hd (u : V) (hu : ‖u‖ ≤ r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) (hsub ⟨hp,by simpa using hu⟩)).differentiableAt (by simp)
  have hder (u : V) (hu : u ∈ closedBall (0 : V) ‖z‖) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ C*‖z‖ := by
    have hu' : ‖u‖ ≤ ‖z‖ := by simpa using hu
    rw [← dpos_eq_at F p u (hd u (hu'.trans hz))]
    exact (hlin p hp u (hu'.trans hz)).trans (mul_le_mul_of_nonneg_left hu' hC)
  have hh := (convex_closedBall (0 : V) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u ((by simpa using hu : ‖u‖ ≤ ‖z‖).trans hz)).comp u
      ((differentiableAt_const p).prodMk differentiableAt_id)) hder
    (show (0 : V) ∈ closedBall 0 ‖z‖ by simp)
    (show z ∈ closedBall 0 ‖z‖ by simp)
  simpa [pow_two,mul_assoc] using hh

end FiniteDimensionalDirections
open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

lemma normalMap_joint (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun x : Space × Space => normalMap g B x.1 x.2) :=
  contDiff_fst.add ((hB.comp contDiff_fst).clm_apply
    (jointJet_contDiff (metricJet g B) (metricJet_contDiff g B hg hB)))

lemma normalDifferential_joint (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun x : Space × Space => normalDifferential g B x.1 x.2) := by
  have hJ : ContDiff ℝ ∞ (fun x : Space × Space => normalJacobian (metricJet g B x.1) x.2) :=
    contDiff_const.sub (((christoffel_contDiff.comp (metricJet_contDiff g B hg hB)).comp
      contDiff_fst).clm_apply contDiff_snd)
  exact (hB.comp contDiff_fst).clm_comp hJ

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def regularSet (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) : Set (Space × Space) :=
  {x | normalMap g B x.1 x.2 ∈ D.domain ∧ (normalDifferential g B x.1 x.2).IsInvertible}

lemma regularSet_open (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (regularSet J α ht p D g B) := by
  exact (D.domain_open.preimage (normalMap_joint g B hg hB).continuous).inter
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Space) (F := Space)).preimage
      (normalDifferential_joint g B hg hB).continuous)

lemma regularSet_center (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hq : q ∈ D.domain) (hBq : (B q).IsInvertible) :
    (q,0) ∈ regularSet J α ht p D g B := by
  exact ⟨by simpa using hq,by simpa using hBq⟩

lemma pulledA_joint (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ regularSet J α ht p D g B) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun y : Space × Space => pulledA J α ht p D g B y.1 i y.2) x := by
  change ContDiffAt ℝ ∞ (fun y : Space × Space => ∑ k,
    ((normalDifferential g B y.1 y.2).inverse (EuclideanEnergy.e k) i) •
      HodgeChart.normalA J α ht p D k (normalMap g B y.1 y.2)) x
  apply ContDiffAt.sum
  intro k _
  have hinv := hx.2.contDiffAt_map_inverse.comp x (normalDifferential_joint g B hg hB).contDiffAt
  have hc := (HodgeChart.normalA_smooth J α ht p D k).contDiffAt
    (D.domain_open.mem_nhds hx.1)
  exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp x
    (hinv.clm_apply contDiffAt_const)).smul
      (hc.comp x (normalMap_joint g B hg hB).contDiffAt)

lemma pulledB_joint (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ regularSet J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun y : Space × Space => pulledB J α ht p D g B y.1 y.2) x := by
  exact ((HodgeChart.normalB_smooth J α hs ht p D).contDiffAt
    (D.domain_open.mem_nhds hx.1)).comp x (normalMap_joint g B hg hB).contDiffAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
