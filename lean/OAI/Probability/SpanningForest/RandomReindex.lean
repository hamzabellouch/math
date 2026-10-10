import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.RandomReindex

theorem map_prod_fiberwise
    {K V W : Type*} [MeasurableSpace K] [MeasurableSpace V] [MeasurableSpace W]
    (κ : Measure K) (ν : Measure V) (η : Measure W)
    [SFinite ν] [SFinite η]
    (f : K → V → W)
    (hf : Measurable (fun p : K × V => f p.1 p.2))
    (hmap : ∀ᵐ k ∂κ, ν.map (f k) = η) :
    (κ.prod ν).map (fun p : K × V => (p.1, f p.1 p.2)) = κ.prod η := by
  have hpair : Measurable (fun p : K × V => (p.1, f p.1 p.2)) :=
    measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hpair hs, Measure.prod_apply (hs.preimage hpair),
    Measure.prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hmap] with k hk
  change ν ((f k) ⁻¹' (Prod.mk k ⁻¹' s)) = η (Prod.mk k ⁻¹' s)
  have hfk : Measurable (f k) := hf.comp measurable_prodMk_left
  rw [← hk, Measure.map_apply hfk (hs.preimage measurable_prodMk_left)]

theorem measurable_random_eval
    {K J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (a : K → J) (ha : Measurable a) :
    Measurable (fun p : K × (J → V) => p.2 (a p.1)) := by
  have hev : Measurable (fun p : J × (J → V) => p.2 p.1) :=
    measurable_from_prod_countable_right (fun j => measurable_pi_apply j)
  exact hev.comp ((ha.comp measurable_fst).prodMk measurable_snd)

theorem measurable_select
    {K I J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i)) :
    Measurable (fun p : K × (J → V) => fun i => p.2 (a p.1 i)) := by
  exact Measurable.of_eval (fun i => measurable_random_eval (fun k => a k i) (ha i))

theorem map_random_injective_reindex
    {K I J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (κ : Measure K) (ν : Measure V) [IsProbabilityMeasure ν]
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i))
    (hinj : ∀ᵐ k ∂κ, Function.Injective (a k)) :
    (κ.prod (Measure.infinitePi (fun _ : J => ν))).map
        (fun p : K × (J → V) => (p.1, fun i => p.2 (a p.1 i))) =
      κ.prod (Measure.infinitePi (fun _ : I => ν)) := by
  apply map_prod_fiberwise κ (Measure.infinitePi (fun _ : J => ν))
    (Measure.infinitePi (fun _ : I => ν))
    (fun k v i => v (a k i)) (measurable_select a ha)
  filter_upwards [hinj] with k hk
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : J => ν) hk

theorem map_random_injective_reindex_of_joint_law
    {Ω K I J V : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    [MeasurableSpace V]
    (P : Measure Ω) (κ : Measure K) (ν : Measure V) [IsProbabilityMeasure ν]
    (key : Ω → K) (pool : Ω → J → V)
    (hkey : Measurable key) (hpool : Measurable pool)
    (hlaw : P.map (fun ω => (key ω, pool ω)) =
      κ.prod (Measure.infinitePi (fun _ : J => ν)))
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i))
    (hinj : ∀ᵐ k ∂κ, Function.Injective (a k)) :
    P.map (fun ω => (key ω, fun i => pool ω (a (key ω) i))) =
      κ.prod (Measure.infinitePi (fun _ : I => ν)) := by
  have hm : Measurable (fun p : K × (J → V) =>
      (p.1, fun i => p.2 (a p.1 i))) :=
    measurable_fst.prodMk (measurable_select a ha)
  rw [← map_random_injective_reindex κ ν a ha hinj, ← hlaw,
    Measure.map_map hm (hkey.prodMk hpool)]
  rfl

theorem prod_diagonal_null
    {V : Type*} [MeasurableSpace V] [MeasurableEq V]
    (ν : Measure V) [SFinite ν] [NullSingletonClass ν] :
    (ν.prod ν) (Set.diagonal V) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have hsection (v : V) : Prod.mk v ⁻¹' Set.diagonal V = {v} := by
    ext w
    simp [Set.diagonal, eq_comm]
  simp [hsection]

theorem ae_injective_infinitePi
    {J V : Type*} [Countable J] [MeasurableSpace V] [MeasurableEq V]
    (ν : Measure V) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), Function.Injective v := by
  have hne (i j : J) (hij : i ≠ j) :
      ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), v i ≠ v j := by
    have hd := prod_diagonal_null ν
    rw [← Measure.infinitePi_map_eval_prod (P := fun _ : J => ν) hij,
      Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
        measurableSet_diagonal] at hd
    simpa only [ae_iff, Set.preimage, Set.mem_diagonal_iff, not_not] using hd
  have hall : ∀ i j : J,
      ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), i ≠ j → v i ≠ v j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · exact (hne i j hij).mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (hall i))] with v hv
  intro i j heq
  by_contra hij
  exact hv i j hij heq

end Problem336.RandomReindex

end

end OAI
