import OAI.Probability.FreeIsing.Estimates.RandomIndexSampling
import OAI.Probability.FreeIsing.Trees.FiniteClusterSelector

namespace OAI

noncomputable section

open MeasureTheory
open scoped Classical

namespace Problem367.FiniteCluster

variable {V I : Type*}

local instance : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

abbrev FiberCompatible (D : Finset V) (r : V → I) (eta : V → IsingSpin) : Prop :=
  RandomIndexSampling.Consistent D r eta

theorem fiberCompatible_of_prescription {D : Finset V} {r : V → I}
    {eta : V → IsingSpin} {seeds : I → IsingSpin}
    (h : ∀ v ∈ D, seeds (r v) = eta v) : FiberCompatible D r eta := by
  intro v hv w hw hr
  rw [← h v hv, ← h w hw, hr]

theorem fairColor_cylinder [Countable I]
    (D : Finset V) (r : V → I) (eta : V → IsingSpin) :
    (Measure.infinitePi (fun _ : I => uniform01))
      {U | ∀ v ∈ D, fairSpin (U (r v)) = eta v} =
      if FiberCompatible D r eta then
        (1 / 2 : ENNReal) ^ (D.image r).card else 0 := by
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  let ν := Measure.map fairSpin uniform01
  have hmass : ∀ a, ν {a} = (1 / 2 : ENNReal) := by
    intro a
    rw [show ν = Measure.map fairSpin uniform01 from rfl,
      Measure.map_apply measurable_fairSpin (measurableSet_singleton a)]
    exact fairSpin_mass a
  have h := RandomIndexSampling.finite_cylinder ν (1 / 2) hmass D r eta
  have hmap := Measure.infinitePi_map_pi (fun _ : I => uniform01)
    (fun _ : I => measurable_fairSpin)
  have hset : MeasurableSet {u : I → IsingSpin | ∀ v ∈ D, u (r v) = eta v} := by
    have hC : MeasurableSet {x : V → IsingSpin | ∀ v ∈ D, x v = eta v} :=
      MeasurableSet.pi D.countable_toSet (fun _ _ => measurableSet_singleton _)
    have hr : Measurable (fun u : I → IsingSpin => fun v => u (r v)) :=
      Measurable.of_eval fun v => measurable_pi_apply (r v)
    exact hr hC
  have hf : Measurable (fun U : I → ℝ => fun i => fairSpin (U i)) :=
    Measurable.of_eval fun i => measurable_fairSpin.comp (measurable_pi_apply i)
  rw [← hmap, Measure.map_apply hf hset] at h
  exact h

theorem map_fairColor_cylinder [Countable I]
    (D : Finset V) (r : V → I) (eta : V → IsingSpin) :
    (Measure.map (fun U : I → ℝ => fun v => fairSpin (U (r v)))
      (Measure.infinitePi (fun _ : I => uniform01)))
      {x | ∀ v ∈ D, x v = eta v} =
      if FiberCompatible D r eta then
        (1 / 2 : ENNReal) ^ (D.image r).card else 0 := by
  classical
  have hm : Measurable (fun U : I → ℝ => fun v => fairSpin (U (r v))) :=
    Measurable.of_eval fun v => measurable_fairSpin.comp (measurable_pi_apply (r v))
  have hset : MeasurableSet {x : V → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet
      (fun v _ => (show MeasurableSet ({eta v} : Set IsingSpin) from trivial))
  rw [Measure.map_apply hm hset]
  exact fairColor_cylinder D r eta

theorem random_fairColor_cylinder {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    (μ : Measure Ω) [SFinite μ] (D : Finset V) (r : Ω → V → I)
    (hr : ∀ v, Measurable (fun ω => r ω v)) (eta : V → IsingSpin) :
    (μ.prod (Measure.infinitePi (fun _ : I => uniform01)))
      {z : Ω × (I → ℝ) | ∀ v ∈ D, fairSpin (z.2 (r z.1 v)) = eta v} =
      ∫⁻ ω, if FiberCompatible D (r ω) eta then
        (1 / 2 : ENNReal) ^ (D.image (r ω)).card else 0 ∂μ := by
  let ν := Measure.map fairSpin uniform01
  have hmass : ∀ a, ν {a} = (1 / 2 : ENNReal) := by
    intro a
    rw [show ν = Measure.map fairSpin uniform01 from rfl,
      Measure.map_apply measurable_fairSpin (measurableSet_singleton a)]
    exact fairSpin_mass a
  have hf : Measurable (fun U : I → ℝ => fun i => fairSpin (U i)) :=
    Measurable.of_eval fun i => measurable_fairSpin.comp (measurable_pi_apply i)
  have hP : MeasurePreserving (fun U : I → ℝ => fun i => fairSpin (U i))
      (Measure.infinitePi (fun _ : I => uniform01))
      (Measure.infinitePi (fun _ : I => ν)) :=
    ⟨hf, Measure.infinitePi_map_pi (fun _ : I => uniform01) (fun _ => measurable_fairSpin)⟩
  have hT := (MeasurePreserving.id μ).prod hP
  have hC : MeasurableSet {x : V → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun _ _ => measurableSet_singleton _)
  have hset : MeasurableSet {z : Ω × (I → IsingSpin) | ∀ v ∈ D, z.2 (r z.1 v) = eta v} :=
    (RandomIndexSampling.measurable_select r hr) hC
  have h := RandomIndexSampling.random_finite_cylinder μ ν (1 / 2) hmass D r hr eta
  rw [← hT.map_eq, Measure.map_apply hT.measurable hset] at h
  exact h

def ClusterCompatible (R : V → V → Prop) (D : Finset V) (eta : V → IsingSpin) : Prop :=
  ∀ v ∈ D, ∀ w ∈ D, R v w → eta v = eta w

theorem fiberCompatible_selector_iff {R : V → V → Prop} {marker : V → ℝ}
    (D : Finset V) (eta : V → IsingSpin) (hR : Equivalence R)
    (hfinite : ∀ v ∈ D, {a | R v a}.Finite) (hinj : Function.Injective marker) :
    FiberCompatible D (selector R marker) eta ↔ ClusterCompatible R D eta := by
  constructor
  · intro h v hv w hw hvw
    exact h v hv w hw (selector_eq_of_related hR hvw (hfinite v hv) hinj)
  · intro h v hv w hw heq
    exact h v hv w hw ((selector_eq_iff_related hR (hfinite v hv) (hfinite w hw) hinj).mp heq)

theorem clusterColor_cylinder [Countable V] {R : V → V → Prop} {marker : V → ℝ}
    (D : Finset V) (eta : V → IsingSpin) (hR : Equivalence R)
    (hfinite : ∀ v ∈ D, {a | R v a}.Finite) (hinj : Function.Injective marker) :
    (Measure.infinitePi (fun _ : V => uniform01))
      {U | ∀ v ∈ D, color R marker (fairSpin ∘ U) v = eta v} =
      if ClusterCompatible R D eta then
        (1 / 2 : ENNReal) ^ (D.image (selector R marker)).card else 0 := by
  classical
  change (Measure.infinitePi (fun _ : V => uniform01))
    {U | ∀ v ∈ D, fairSpin (U (selector R marker v)) = eta v} = _
  rw [fairColor_cylinder, fiberCompatible_selector_iff D eta hR hfinite hinj]

theorem random_clusterColor_cylinder {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) [SFinite μ] (R : Ω → V → V → Prop) (marker : Ω → V → ℝ)
    (D : Finset V) (eta : V → IsingSpin)
    (hRm : ∀ v a, MeasurableSet {ω | R ω v a})
    (hmarker : ∀ a, Measurable (fun ω => marker ω a))
    (hR : ∀ᵐ ω ∂μ, Equivalence (R ω))
    (hfinite : ∀ᵐ ω ∂μ, ∀ v ∈ D, {a | R ω v a}.Finite)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective (marker ω)) :
    (μ.prod (Measure.infinitePi (fun _ : V => uniform01)))
      {z : Ω × (V → ℝ) | ∀ v ∈ D,
        color (R z.1) (marker z.1) (fairSpin ∘ z.2) v = eta v} =
      ∫⁻ ω, if ClusterCompatible (R ω) D eta then
        (1 / 2 : ENNReal) ^ (D.image (selector (R ω) (marker ω))).card else 0 ∂μ := by
  change (μ.prod (Measure.infinitePi (fun _ : V => uniform01)))
    {z : Ω × (V → ℝ) | ∀ v ∈ D,
      fairSpin (z.2 (selector (R z.1) (marker z.1) v)) = eta v} = _
  rw [random_fairColor_cylinder μ D (fun ω => selector (R ω) (marker ω))
    (measurable_selector R marker hRm hmarker) eta]
  apply lintegral_congr_ae
  filter_upwards [hR, hfinite, hinj] with ω hRω hfω hiω
  rw [fiberCompatible_selector_iff D eta hRω hfω hiω]

end Problem367.FiniteCluster

end

end OAI
