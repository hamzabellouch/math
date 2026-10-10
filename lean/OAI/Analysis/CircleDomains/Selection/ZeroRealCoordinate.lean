import OAI.Analysis.CircleDomains.Modulus.RealBarrierTests
import OAI.Analysis.CircleDomains.Selection.FreeLevelSections

namespace OAI

/-! A zero coordinate occupies unused selection slots. Its new-level failure
event is contained in the single zero circle level, hence has zero measure. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def PhysicalRealCoordinate.zero (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) :
    PhysicalRealCoordinate d π where
  quotient := fun _ => 0
  quotient_continuous := continuousOn_const
  quotient_unit := fun _ => ⟨le_rfl, zero_le_one⟩
  physical := fun _ => 0
  physical_measurable := measurable_const
  physical_smooth := contDiffOn_const
  physical_energy := by
    have he : FiniteTransfer.planarGradient (fun _ : ℝ × ℝ => (0 : ℝ)) = 0 := by
      funext x
      simp [FiniteTransfer.planarGradient]
    rw [he]
    exact MemLp.zero
  pullback := fun _ _ => rfl

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem circleBandGraph_zero_subset (U : Set Sphere) :
    circleBandGraph U (fun _ => 0) ⊆ {p : Sphere × UnitAddCircle | p.2 = 0} := by
  rintro _ ⟨⟨x, t⟩, ht, rfl⟩
  obtain ⟨a, b, s, ha, hb, _, he⟩ := mem_intervalFiberHull_iff.mp ht
  have hza : a = 0 := clusterGraph_fiber_eq_of_continuousAt continuousAt_const ha
  have hzb : b = 0 := clusterGraph_fiber_eq_of_continuousAt continuousAt_const hb
  have ht0 : t = 0 := by simpa only [hza, hzb, mul_zero, add_zero] using he
  change (t : UnitAddCircle) = 0
  rw [ht0]
  rfl

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem zero_coordinate_compatibility (U F : Set Sphere) {I : Type*}
    (R : I → Set (Sphere × UnitAddCircle)) (n : ℕ) (labels : Fin n → I) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph U (fun _ => 0)) R labels) = 0 := by
  apply measure_mono_null (t := ({0} : Set UnitAddCircle) ×ˢ univ)
  · rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
    exact ⟨circleBandGraph_zero_subset U hx.2.1, mem_univ _⟩
  · simp only [Measure.prod_prod, unitAddCircle_volume_singleton, zero_mul]

def UngatedRealTest.zeroTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) : UngatedRealTest d π EStar where
  coordinate := PhysicalRealCoordinate.zero d π
  region := ∅
  region_open := isOpen_empty
  zero := fun _ _ => rfl
  one := fun _ hx => hx.1.elim
  exclusions := ∅
  exclusions_countable := countable_empty
  weight := fun _ => 0
  weight_finite := by simp
  weight_support := by simp
  band_bound := by
    intro x hx
    simp only [PhysicalRealCoordinate.zero]
    by_cases h : NeBot (𝓝[d.quotientDomain] x)
    · let := h
      simp
    · have he : 𝓝[d.quotientDomain] x = ⊥ := not_neBot.mp h
      simp only [he, limsup_eq, liminf_eq, eventually_bot, ofPred_true]
      rw [Real.sInf_of_not_bddBelow not_bddBelow_univ,
        Real.sSup_of_not_bddAbove not_bddAbove_univ]
      norm_num

end CircleDomainRigidity

end

end OAI
