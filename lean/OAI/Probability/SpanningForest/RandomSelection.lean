import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.RandomSelection

variable {K I J X : Type*}
variable [MeasurableSpace K] [MeasurableSpace J] [MeasurableSpace X]
variable [Countable J] [MeasurableSingletonClass J]

lemma measurable_selected_array (s : K → I → J)
    (hs : ∀ i, Measurable (fun k => s k i)) :
    Measurable (fun p : K × (J → X) => fun i => p.2 (s p.1 i)) := by
  apply measurable_pi_iff.mpr
  intro i
  have heval : Measurable (fun p : (J → X) × J => p.1 p.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact heval.comp (measurable_snd.prodMk ((hs i).comp measurable_fst))

theorem measurePreserving_selected_array
    (μ : Measure K) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (s : K → I → J) (hs : ∀ i, Measurable (fun k => s k i))
    (hinj : ∀ᵐ k ∂μ, Function.Injective (s k)) :
    MeasurePreserving
      (fun p : K × (J → X) => (p.1, fun i => p.2 (s p.1 i)))
      (μ.prod (Measure.infinitePi (fun _ : J => ν)))
      (μ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  refine (MeasurePreserving.id μ).skew_product
    (μc := Measure.infinitePi (fun _ : J => ν))
    (μd := Measure.infinitePi (fun _ : I => ν))
    (g := fun k (v : J → X) i => v (s k i))
    (measurable_selected_array s hs) ?_
  filter_upwards [hinj] with k hk
  exact Measure.map_infinitePi_infinitePi_of_inj hk

theorem map_selected_array
    (μ : Measure K) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (s : K → I → J) (hs : ∀ i, Measurable (fun k => s k i))
    (hinj : ∀ᵐ k ∂μ, Function.Injective (s k)) :
    (μ.prod (Measure.infinitePi (fun _ : J => ν))).map
      (fun p : K × (J → X) => (p.1, fun i => p.2 (s p.1 i))) =
      μ.prod (Measure.infinitePi (fun _ : I => ν)) :=
  (measurePreserving_selected_array μ ν s hs hinj).map_eq

theorem measurePreserving_selection
    (μ : Measure K) [IsProbabilityMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (s : K → I → J) (hs : ∀ i, Measurable (fun k => s k i))
    (hinj : ∀ᵐ k ∂μ, Function.Injective (s k)) :
    MeasurePreserving
      (fun p : K × (J → X) => fun i => p.2 (s p.1 i))
      (μ.prod (Measure.infinitePi (fun _ : J => ν)))
      (Measure.infinitePi (fun _ : I => ν)) := by
  exact (measurePreserving_snd (μ := μ)
    (ν := Measure.infinitePi (fun _ : I => ν))).comp
    (measurePreserving_selected_array μ ν s hs hinj)

theorem map_selected_array_of_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Measure K) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (keys : Ω → K) (pool : Ω → J → X)
    (hkeys : Measurable keys) (hpool : Measurable pool)
    (hlaw : P.map (fun ω => (keys ω, pool ω)) =
      μ.prod (Measure.infinitePi (fun _ : J => ν)))
    (s : K → I → J) (hs : ∀ i, Measurable (fun k => s k i))
    (hinj : ∀ᵐ k ∂μ, Function.Injective (s k)) :
    P.map (fun ω => (keys ω, fun i => pool ω (s (keys ω) i))) =
      μ.prod (Measure.infinitePi (fun _ : I => ν)) := by
  have hm := (measurePreserving_selected_array μ ν s hs hinj).measurable
  have heq := Measure.map_map (μ := P) hm (hkeys.prodMk hpool)
  rw [hlaw, map_selected_array μ ν s hs hinj] at heq
  exact heq.symm

end Problem336.RandomSelection

end

end OAI
