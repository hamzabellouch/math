import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PairingSmooth
import OAI.Geometry.TamingCompatibility.Charts.ChartUnitaryData

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open Bundle ManifoldForms ManifoldLocalization ManifoldVolume ManifoldHodge
open Set MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

def cutoffForm {k : ℕ} (p : A.centers) (a : ManifoldForms.Form X k) : ManifoldForms.Form X k :=
  fun x => A.partition p x • a x

lemma cutoffForm_smooth {k : ℕ} (p : A.centers) {a : ManifoldForms.Form X k} (ha : Smooth a) :
    Smooth (cutoffForm A p a) := Smooth.fun_smul (A.partition p).contMDiff ha

lemma cutoffForm_anti (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a) :
    antiInvariantPart J (cutoffForm A p a) = cutoffForm A p a := by
  funext x
  have h := congrFun ha x
  change (1/2:ℝ) • (A.partition p x • a x -
    (A.partition p x • a x).compContinuousLinearMap (J.endomorphism x)) = A.partition p x • a x
  have hc : (A.partition p x • a x).compContinuousLinearMap (J.endomorphism x) =
      A.partition p x • (a x).compContinuousLinearMap (J.endomorphism x) := by ext v; rfl
  rw [hc]
  change (1/2:ℝ) • (a x - (a x).compContinuousLinearMap (J.endomorphism x)) = a x at h
  ext v
  have hv := congrArg (fun q => q v) h
  simp only [ContinuousAlternatingMap.smul_apply,ContinuousAlternatingMap.sub_apply,
    smul_eq_mul] at hv ⊢
  calc
    _ = A.partition p x * ((1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v)) := by ring
    _ = _ := congrArg (A.partition p x * ·) hv

lemma pairing_chart (p : X) {k : ℕ} (hk : k=1 ∨ k=2) (a b : ManifoldForms.Form X k)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (ManifoldForms.pullback b (extChartAt Model p).symm z) =
      GeometricAdjoint.pairing J α ht a b ((extChartAt Model p).symm z) := by
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  rcases hk with rfl | rfl
  · have h := MetricForms.pairing_one_comp (E := Space) (D := Space)
      (coordinateMetric J α ht p z) (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
      L (coordinateMetric_pullback J α ht p hz) (by simp [Space])
      (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
    rw [hL] at h
    exact h
  · have h := MetricForms.pairing_two_comp (E := Space) (D := Space)
      (coordinateMetric J α ht p z) (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
      L (coordinateMetric_pullback J α ht p hz) (by simp [Space])
      (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
    rw [hL] at h
    exact h

lemma localizedPairing_eq_coordinateIntegrand (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    (a : ManifoldForms.Form X k) :
    (fun z => chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) =
    coordinateIntegrand J α p.val (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) := by
  funext z
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · unfold localizedFunction coordinateIntegrand
    rw [indicator_of_mem hz,indicator_of_mem hz,MetricForms.pairing_smul_left,
      MetricForms.pairing_smul_right,pairing_chart J α ht p.val hk a a hz]
    ring
  · unfold localizedFunction coordinateIntegrand
    rw [indicator_of_notMem hz,indicator_of_notMem hz]
    simp only [MetricForms.pairing_self_eq_zero _ _ |>.mpr rfl,mul_zero]

lemma cutoff_square_tsupport (p : A.centers) :
    tsupport (fun x => (A.partition p x)^2) ⊆ tsupport (A.partition p) := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := fun x => A.partition p x) (g := fun x => A.partition p x))

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (hs : IsSmooth α)

include hs in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localizedPairing_integrable (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    {a : ManifoldForms.Form X k} (ha : Smooth a) :
    Integrable (fun z => chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) := by
  rw [localizedPairing_eq_coordinateIntegrand A J α ht p hk a]
  apply coordinateIntegrand_integrable J α hs ht p.val
  · apply ((A.partition p).contMDiff.continuous.pow 2).mul
    rcases hk with rfl|rfl
    · exact (GeometricAdjoint.pairing_one_smooth J α hs ht ha ha).continuous
    · exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous
  · apply (tsupport_mul_subset_left).trans
    exact (cutoff_square_tsupport A p).trans (A.subordinate p)

include hs in

lemma integral_localizedPairing (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    {a : ManifoldForms.Form X k} (ha : Smooth a) :
    (∫ z, chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) =
    ∫ x, (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α := by
  rw [localizedPairing_eq_coordinateIntegrand A J α ht p hk a]
  have hc : Continuous (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) := by
    apply ((A.partition p).contMDiff.continuous.pow 2).mul
    rcases hk with rfl|rfl
    · exact (GeometricAdjoint.pairing_one_smooth J α hs ht ha ha).continuous
    · exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous
  have hp : tsupport (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) ⊆
      (extChartAt Model p.val).source :=
    tsupport_mul_subset_left.trans ((cutoff_square_tsupport A p).trans (A.subordinate p))
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _ hc hp,
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ContinuousAlternatingMap
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_anti (p : A.centers) {a : TwoForm X}
    (ha : antiInvariantPart J a = a) {x : Space} (hx : x ∈ (extChartAt Model p.val).target) :
    (localizedFunction A p a x).compContinuousLinearMap (coordinateJ J p.val x) =
      -localizedFunction A p a x := by
  have hj : TamingCompatibility.jAction J a = -a := by
    calc TamingCompatibility.jAction J a = a - (2 : ℝ) • antiInvariantPart J a := by
          unfold antiInvariantPart
          module
         _ = -a := by rw [ha]; module
  have hp := pullback_jAction_chart (⟨J.endomorphism,J.square,J.smooth⟩ :
      SmoothAlmostComplex.AlmostComplexStructure X) a p.val hx
  change ManifoldForms.pullback (TamingCompatibility.jAction J a) (extChartAt Model p.val).symm x =
    (ManifoldForms.pullback a (extChartAt Model p.val).symm x).compContinuousLinearMap
      (coordinateJ J p.val x) at hp
  rw [hj] at hp
  have hn : ManifoldForms.pullback (-a) (extChartAt Model p.val).symm x =
    -ManifoldForms.pullback a (extChartAt Model p.val).symm x := rfl
  rw [hn] at hp
  unfold localizedFunction
  rw [indicator_of_mem hx]
  ext v
  change A.partition p ((extChartAt Model p.val).symm x) *
      ((ManifoldForms.pullback a (extChartAt Model p.val).symm x).compContinuousLinearMap
        (coordinateJ J p.val x)) v = _
  rw [← hp]
  simp only [ContinuousAlternatingMap.neg_apply,ContinuousAlternatingMap.smul_apply,
    smul_eq_mul,mul_neg]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma scalar_expansion (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a)
    (x : Space) : localizedFunction A p a x =
      scalar A J α ht D p a 2 x • realPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) +
      scalar A J α ht D p a 3 x • imagPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) := by
  by_cases hx : x ∈ (D p).domain
  · simp only [scalar,indicator_of_mem hx]
    obtain ⟨h0,h1,h2,h3⟩ := (D p).frame_complex x hx
    exact expansion (coordinateMetric J α ht p.val x) (by simp [Space])
      (fun i => (D p).frame i x) ((D p).frame_gram x hx)
      (coordinateJ J p.val x) h0 h1 h2 h3 (localizedFunction A p a x)
      (localizedFunction_anti A J p ha ((D p).domain_subset hx))
  · have hK : x ∉ coordinateSupport A p := fun h => hx (coordinateSupport_domain A J α ht D hD p h)
    rw [localizedFunction_zero_off A p a hK,scalar_zero_off A J α ht D p a 2 hK,
      scalar_zero_off A J α ht D p a 3 hK,zero_smul,zero_smul,add_zero]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
