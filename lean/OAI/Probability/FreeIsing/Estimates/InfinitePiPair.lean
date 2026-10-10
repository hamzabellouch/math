import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

variable {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem infinitePi_map_pair_arrays
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      (fun p : (s → A) × (s → B) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_pairs
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
