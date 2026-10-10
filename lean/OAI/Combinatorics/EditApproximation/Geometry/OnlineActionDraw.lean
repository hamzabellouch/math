import OAI.Combinatorics.EditApproximation.Geometry.BandRegret
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The finite rational optimizer samples actual band actions, retaining their labels through ties. -/

namespace EditApproximation

open Finset

theorem argmax_map_commutes {α β γ : Type*} [Preorder γ] [DecidableLT γ]
    (mapping : α → β) (score : β → γ) (values : List α) :
    (values.map mapping).argmax score = (values.argmax (fun a => score (mapping a))).map mapping := by
  induction values using List.reverseRecOn with
  | nil => rfl
  | append_singleton values a ih =>
    rw [List.map_append, List.map_singleton, List.argmax_concat, List.argmax_concat, ih]
    cases h : values.argmax (fun a => score (mapping a)) with
    | none => rfl
    | some selected =>
      simp only [Option.map_some]
      split_ifs <;> rfl



theorem finiteOptimizerAction_spec {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G j : ℕ) :
    finiteOptimizerAction band hband mass linear G j ∈ band ∧
      actionVector mass (finiteOptimizerAction band hband mass linear G j) =
        finiteOptimizerSelection (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G j := by
  let coordinates := bandCoordinates band.toFinset
  let vertices := band.map (actionVector mass)
  let gradient := rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j)
  let score := fun action : β → σ => ∑ coordinate ∈ coordinates,
    gradient coordinate * actionVector mass action coordinate
  have hmap := argmax_map_commutes (actionVector mass)
    (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate) band
  cases harg : band.argmax score with
  | none => exact False.elim (hband (List.argmax_eq_none.mp harg))
  | some action =>
    have hmem : action ∈ band := List.argmax_mem (by rw [harg]; simp)
    have hvalue : finiteOptimizerAction band hband mass linear G j = action := by
      simp only [finiteOptimizerAction, score, coordinates, vertices, gradient] at harg ⊢
      rw [harg]
      rfl
    refine ⟨hvalue.symm ▸ hmem, ?_⟩
    rw [hvalue]
    unfold finiteOptimizerSelection rationalLinearizationMaximizer
    change actionVector mass action = (vertices.argmax
      (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate)).getD (fun _ => 0)
    change vertices.argmax (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate) =
      (band.argmax score).map (actionVector mass) at hmap
    rw [hmap, harg]
    rfl



theorem finiteOptimizerActionDraw_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    finiteOptimizerActionDraw band hband mass linear G K integer ∈ band :=
  (finiteOptimizerAction_spec band hband mass linear G (triangularChoice K integer).val).1

theorem finiteOptimizerActionDraw_mean {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K) (coordinate : β × σ) :
    (∑ integer : Fin (optimizerTriangularMass K),
      actionVector mass (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate) /
        optimizerTriangularMass K =
      finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G K coordinate := by
  have hselected (integer : Fin (optimizerTriangularMass K)) :
      actionVector mass (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate =
        finiteOptimizerSelection (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G
          (triangularChoice K integer).val coordinate :=
    congrFun (finiteOptimizerAction_spec band hband mass linear G (triangularChoice K integer).val).2 coordinate
  simp_rw [hselected]
  exact finiteRationalOptimizer_sampler_mean _ _ linear G K hK coordinate

end EditApproximation

end OAI
