import OAI.Analysis.CircleDomains.Transfer.ScalarHoleFillings

namespace OAI

/-! Bounded measurable fillings on the whole plane, equal to the clipped
transferred scalar in the domain and constant on each actual round hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def clipScalar (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clipScalar_lipschitz : LipschitzWith 1 clipScalar :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem clipScalar_mem (t : ℝ) : clipScalar t ∈ Icc 0 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clipScalar_eq {t : ℝ} (ht : t ∈ Icc 0 1) : clipScalar t = t := by
  rw [clipScalar, min_eq_right ht.2, max_eq_right ht.1]

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem transferred_continuousOn (i : Fin m) (n : ℕ) :
    ContinuousOn (R.transferred i n) (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  rw [transferred, transported_sphereRealFunction_eq]
  exact ((R.model.stages n).transported_smooth (prefixIndex (R.index i) n)).continuousOn.comp
    Complex.equivRealProdCLM.continuous.continuousOn (fun z hz => by
      simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz)

namespace HoleFilling
variable {R} {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

def filled (z : ℂ) : ℝ :=
  (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
    (clipScalar ∘ R.transferred i n) z +
    ∑' s, (closedBall (F.center s) (F.radius s)).indicator (fun _ => clipScalar (F.value s)) z

theorem filled_on_domain {z : ℂ} (hz : (z : Sphere) ∈ (R.model.stages n).domain) :
    F.filled z = clipScalar (R.transferred i n z) := by
  have hnot : z ∉ ⋃ s, closedBall (F.center s) (F.radius s) := by
    rw [← mem_compl_iff, ← F.complement]
    exact hz
  have hzero : ∀ s, (closedBall (F.center s) (F.radius s)).indicator
      (fun _ => clipScalar (F.value s)) z = 0 := by
    intro s
    exact indicator_of_notMem (fun h => hnot (mem_iUnion.mpr ⟨s, h⟩)) _
  have hz' : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := hz
  simp only [filled, indicator_of_mem hz', hzero, tsum_zero, add_zero, comp_apply]

theorem filled_on_hole (s : (R.model.stages n).indices) {z : ℂ}
    (hz : z ∈ closedBall (F.center s) (F.radius s)) : F.filled z = clipScalar (F.value s) := by
  have hnot : z ∉ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := by
    rw [F.complement]
    exact fun h => h (mem_iUnion.mpr ⟨s, hz⟩)
  have hother : ∀ t ≠ s, (closedBall (F.center t) (F.radius t)).indicator
      (fun _ => clipScalar (F.value t)) z = 0 := by
    intro t hts
    exact indicator_of_notMem (fun ht => disjoint_left.mp (F.disjoint hts) ht hz) _
  rw [filled, indicator_of_notMem hnot, zero_add, tsum_eq_single s hother, indicator_of_mem hz]

theorem filled_mem (z : ℂ) : F.filled z ∈ Icc 0 1 := by
  by_cases hz : (z : Sphere) ∈ (R.model.stages n).domain
  · rw [F.filled_on_domain hz]
    exact clipScalar_mem _
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      by_contra h
      exact hz ((show z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain from
        F.complement.symm ▸ h))
    obtain ⟨s, hs⟩ := mem_iUnion.mp hout
    rw [F.filled_on_hole s hs]
    exact clipScalar_mem _

theorem filled_measurable : Measurable F.filled := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hc := clipScalar_lipschitz.continuous.comp_continuousOn (R.transferred_continuousOn i n)
  have hm : Measurable ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
      (clipScalar ∘ R.transferred i n)) := by
    have he : ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
        (clipScalar ∘ R.transferred i n)) =
        ((((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).piecewise
          (clipScalar ∘ R.transferred i n) (fun _ => 0)) := by
      funext z
      by_cases hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain <;> simp [hz]
    rw [he]
    exact hc.measurable_piecewise continuousOn_const hU.measurableSet
  exact hm.add (Measurable.tsum fun s => measurable_const.indicator measurableSet_closedBall)

theorem filled_memLp {p : ℝ≥0∞} {μ : Measure ℂ} [IsFiniteMeasure μ] : MemLp F.filled p μ := by
  apply MemLp.of_bound F.filled_measurable.aestronglyMeasurable 1
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
    exact (F.filled_mem z).2

end HoleFilling
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
