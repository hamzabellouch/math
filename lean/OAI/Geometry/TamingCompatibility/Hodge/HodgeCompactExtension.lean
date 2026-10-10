import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FirstMatrixJoint
import OAI.Geometry.TamingCompatibility.Concentration.HodgeWeakResidual

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open Set Filter
open scoped Manifold ContDiff Topology
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma exists_compact_smooth_extension {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  have hgsub : tsupport (fun x => φ x • f x) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (by simp [hφzero x hn])
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),
    hOc.of_isClosed_subset (isClosed_tsupport _) hgsub,hgsub.trans hOU,?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_congr_nhds (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) {u v : V → W} {x : V} (h : u =ᶠ[𝓝 x] v) :
    differential e a b u x = differential e a b v x := by
  simp only [differential,h.fderiv_eq,h.eq_of_nhds]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_zero_off (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (u : V → W) {x : V} (hx : x ∉ tsupport u) :
    differential e a b u x = 0 := by
  have he : u =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [differential_congr_nhds e a b he]
  simp [differential]

variable (μ : Measure V) [IsAddHaarMeasure μ]
lemma integral_square_residual_local {U K : Set V} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (k d r η : V → W)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
    (hd : ContinuousOn d U) (hη : ContDiffOn ℝ ∞ η U)
    (hks : tsupport k ⊆ K) (hds : Function.support d ⊆ K) (hrs : Function.support r ⊆ K)
    (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hres : ∀ x ∈ U, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
    (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) +
      (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
      ∫ x, ρ x * ⟪η x,r x⟫ ∂μ := by
  obtain ⟨η',hη',hc,hsupp,he⟩ := exists_compact_smooth_extension hU hK hKU hη
  have hi := integral_square_residual μ hU e a b ρ k d r η' ha hb hρ hk
    (fun x hx => (hd x (hsupp hx)).continuousAt (hU.mem_nhds (hsupp hx)))
    hη' hc hsupp hρ0 (fun x hx => hres x (hsupp hx))
  have hid : (fun x => ρ x * ⟪η' x,d x⟫) = (fun x => ρ x * ⟪η x,d x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [(he x hx).eq_of_nhds]
    · have hz : d x = 0 := by by_contra hn; exact hx (hds hn)
      simp [hz]
  have hir : (fun x => ρ x * ⟪η' x,r x⟫) = (fun x => ρ x * ⟪η x,r x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [(he x hx).eq_of_nhds]
    · have hz : r x = 0 := by by_contra hn; exact hx (hrs hn)
      simp [hz]
  have hik : (fun x => ρ x * ⟪differential e a b η' x,differential e a b k x⟫) =
      (fun x => ρ x * ⟪differential e a b η x,differential e a b k x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [differential_congr_nhds e a b (he x hx)]
    · have hz := differential_zero_off e a b k (fun hh => hx (hks hh))
      simp [hz]
  rwa [hid,hir,hik] at hi

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

def normalDomain : Set (Space × Space) :=
  regularSet J α ht p D g B ∩ normalMetric g B ⁻¹' regularMetrics

def normalDensity (x : Space × Space) : ℝ := volumeDensity (normalMetric g B x)
def normalPrincipal (i j : Fin 4) (x : Space × Space) : ℝ := principal (normalMetric g B x) i j

def normalFirst (j : Fin 4) (x : Space × Space) : W →L[ℝ] W :=
  firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B x.1)
    (pulledB J α ht p D g B x.1) (fun z => normalDensity g B (x.1,z)) j x.2

def normalZero (x : Space × Space) : W →L[ℝ] W :=
  zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B x.1)
    (pulledB J α ht p D g B x.1) (fun z => normalDensity g B (x.1,z)) x.2

def normalGauge (x : Space × Space) : W →L[ℝ] W :=
  gauge (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun j => normalFirst J α ht p D g B j (x.1,0))) x.2

def gaugedDomain : Set (Space × Space) :=
  normalDomain J α ht p D g B ∩ (fun x : Space × Space => (x.1,0)) ⁻¹' normalDomain J α ht p D g B

def gaugedFirst (j : Fin 4) (x : Space × Space) : W →L[ℝ] W :=
  gaugeFirst EuclideanEnergy.e (fun i j z => normalPrincipal g B i j (x.1,z))
    (fun j z => normalFirst J α ht p D g B j (x.1,z))
    (fun z => normalGauge J α ht p D g B (x.1,z)) j x.2

def gaugedZero (x : Space × Space) : W →L[ℝ] W :=
  gaugeZero EuclideanEnergy.e (fun i j z => normalPrincipal g B i j (x.1,z))
    (fun j z => normalFirst J α ht p D g B j (x.1,z))
    (fun z => normalZero J α ht p D g B (x.1,z))
    (fun z => normalGauge J α ht p D g B (x.1,z)) x.2

lemma normalDomain_open (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (normalDomain J α ht p D g B) :=
  (regularSet_open J α ht p D g B hg hB).inter
    (regularMetrics_open.preimage (normalMetric_contDiff g B hg hB).continuous)

lemma gaugedDomain_open (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (gaugedDomain J α ht p D g B) :=
  (normalDomain_open J α ht p D g B hg hB).inter
    ((normalDomain_open J α ht p D g B hg hB).preimage (continuous_fst.prodMk continuous_const))

lemma ActualData.metric_zero {q : Space} (hactual : ActualData J α ht p D q g B) :
    normalMetric g B (q,0) = EMetric := by
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  rw [normalMetric_zero,hgact q hqO,hBact q hqO]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact frameMap_metric _ _ (D.frame_gram q (hOD hqO)) v w

lemma ActualData.center {q : Space} (hactual : ActualData J α ht p D q g B) :
    (q,0) ∈ gaugedDomain J α ht p D g B := by
  have hm := hactual.metric_zero J α ht p D g B
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  have hq := hOD hqO
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqO]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hn : (q,0) ∈ normalDomain J α ht p D g B :=
    ⟨regularSet_center J α ht p D g B q hq hBq,by rw [Set.mem_preimage,hm]; exact euclidean_mem_regularMetrics⟩
  exact ⟨hn,hn⟩

lemma normalDensity_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) :
    ContDiffAt ℝ ∞ (normalDensity g B) x :=
  (volumeDensity_contDiffAt_regular hx).comp x (normalMetric_contDiff g B hg hB).contDiffAt

lemma normalPrincipal_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (normalPrincipal g B i j) x :=
  (principal_contDiffAt_regular hx i j).comp x (normalMetric_contDiff g B hg hB).contDiffAt

lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

lemma normalZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalZero J α ht p D g B) x :=
  zeroMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2))

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

lemma gaugedFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (gaugedFirst J α ht p D g B j) x :=
  gaugeFirst_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalGauge J α ht p D g B) (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2) j

lemma gaugedZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (gaugedZero J α ht p D g B) x :=
  gaugeZero_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalZero J α ht p D g B) (normalGauge J α ht p D g B)
    (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalZero_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
