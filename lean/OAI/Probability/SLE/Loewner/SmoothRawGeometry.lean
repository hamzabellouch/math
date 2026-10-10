import OAI.Probability.SLE.Loewner.SmoothRawSimple
import OAI.Probability.SLE.Loewner.SmoothRawTraceInterior
import OAI.Probability.SLE.Geometry.FiniteSimpleSlit

namespace OAI

/-! The raw smooth trace has the topology of a simple slit. Its raw
surviving domain embeds in the geometric unbounded component; equality
of these domains is treated separately. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

theorem RegularSLEPresentation.smooth_raw_free_complement
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ)
    (b : Target.Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (Target.driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) (T : ℝ≥0) (hT : 0 < T) :
    upperHalfPlane \ ((fun s : ℝ≥0 => Target.trace 1 b s) '' Icc 0 T) ⊆
      survivingDomain (fun s : ℝ≥0 => Target.trace 1 b s) T := by
  apply finite_simple_slit_free (fun s => Target.trace 1 b s)
    (Target.continuous_smooth_raw_trace b b' L hd hb)
    (Target.smooth_trace_zero b b' L hd hb) T hT
    (a.smooth_raw_trace_injective hκ b b' L hd hb).injOn
  intro t ht
  exact Target.smooth_raw_trace_mem_upperHalfPlane b t ht.1 b'
    (fun s hs => (hd s hs.1).mono Icc_subset_Ici_self) L.coe_nonneg (fun s hs => hb s hs.1)

theorem RegularSLEPresentation.smooth_raw_surviving_subset_geometric
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ)
    (b : Target.Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (Target.driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) (T : ℝ≥0) (hT : 0 < T) :
    {z | Target.Surviving 1 b z T} ⊆
      survivingDomain (fun s : ℝ≥0 => Target.trace 1 b s) T := by
  intro z hz
  apply a.smooth_raw_free_complement hκ b b' L hd hb T hT
  refine ⟨Target.surviving_mem_upperHalfPlane 1 b z T T.coe_nonneg hz,?_⟩
  rintro ⟨s,hs,he⟩
  have hp := Target.surviving_of_le_time 1 b z s.coe_nonneg hs.2 hz
  change Target.trace 1 b s=z at he
  rw [← he] at hp
  exact (a.smooth_raw_tip_not_surviving hκ b s b'
    (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self) L.coe_nonneg
    (fun t ht => hb t ht.1)) hp

end SLEExactGauge

end

end OAI
