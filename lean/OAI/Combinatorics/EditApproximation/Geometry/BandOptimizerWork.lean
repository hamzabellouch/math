import OAI.Combinatorics.EditApproximation.Numerics.VectorOptimizerWork
import OAI.Combinatorics.EditApproximation.Geometry.BandDimension
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

def restrictOptimizerVector {ι : Type*} {d : ℕ} (coordinates : Vector ι d)
    (values : ι → ℚ) : Vector ℚ d :=
  Vector.ofFn fun i => values (coordinates.get i)

theorem restrictOptimizerVector_get {ι : Type*} {d : ℕ} (coordinates : Vector ι d)
    (values : ι → ℚ) (i : Fin d) :
    (restrictOptimizerVector coordinates values).get i = values (coordinates.get i) :=
  vector_get_ofFn _ _

theorem coordinateVector_sum {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup) (f : ι → ℚ) :
    (∑ i : Fin d, f (coordinates.get i)) = ∑ c ∈ coordinates.toList.toFinset, f c := by
  rw [List.sum_toFinset f hnodup]
  have hcoordinates : coordinates.toList = List.ofFn coordinates.get := by
    rw [← Vector.toList_ofFn]
    congr 1
    exact (Vector.ofFn_getElem).symm
  rw [hcoordinates, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rationalLinearizationMaximizer_restrict {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) :
    rationalLinearizationMaximizer univ
      (vertices.map fun v => fun i => v (coordinates.get i))
      (fun i => gradient (coordinates.get i)) =
    fun i => rationalLinearizationMaximizer coordinates.toList.toFinset vertices gradient
      (coordinates.get i) := by
  have hsum (v : ι → ℚ) :
      (∑ i : Fin d, gradient (coordinates.get i) * v (coordinates.get i)) =
        ∑ c ∈ coordinates.toList.toFinset, gradient c * v c :=
    coordinateVector_sum coordinates hnodup (fun c => gradient c * v c)
  unfold rationalLinearizationMaximizer
  rw [argmax_map_commutes]
  simp only [hsum]
  cases h : vertices.argmax (fun v => ∑ c ∈ coordinates.toList.toFinset, gradient c * v c) with
  | none => rfl
  | some v => rfl

theorem finiteRationalOptimizer_restrict {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer univ (vertices.map fun v => fun i => v (coordinates.get i))
        (fun i => linear (coordinates.get i)) G j =
      fun i => finiteRationalOptimizer coordinates.toList.toFinset vertices linear G j
        (coordinates.get i) := by
  induction j with
  | zero => cases vertices <;> rfl
  | succ j ih =>
    have hgradient :
        rationalSmoothedGradient G (fun i => linear (coordinates.get i))
          (finiteRationalOptimizer univ (vertices.map fun v => fun i => v (coordinates.get i))
            (fun i => linear (coordinates.get i)) G j) =
        fun i => rationalSmoothedGradient G linear
          (finiteRationalOptimizer coordinates.toList.toFinset vertices linear G j)
          (coordinates.get i) := by
      rw [ih]
      rfl
    funext i
    rw [finiteRationalOptimizer, finiteRationalOptimizer, hgradient,
      rationalLinearizationMaximizer_restrict coordinates hnodup]
    simp only [ih]

theorem materializedOptimizerWithWork_restrict_value {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) (i : Fin d) :
    (materializedOptimizerWithWork (vertices.map (restrictOptimizerVector coordinates))
      (restrictOptimizerVector coordinates linear) G j).1.get i =
    finiteRationalOptimizer coordinates.toList.toFinset vertices linear G j (coordinates.get i) := by
  rw [materializedOptimizerWithWork_value]
  have hvertices : (vertices.map (restrictOptimizerVector coordinates)).map Vector.get =
      vertices.map (fun v => fun k => v (coordinates.get k)) := by
    simp only [List.map_map]
    congr 1
    funext v k
    exact restrictOptimizerVector_get coordinates v k
  have hlinear : (restrictOptimizerVector coordinates linear).get =
      fun k => linear (coordinates.get k) := by
    funext k
    exact restrictOptimizerVector_get coordinates linear k
  rw [hvertices, hlinear, finiteRationalOptimizer_restrict coordinates hnodup]

/-- Concrete ordered coordinates; no enumeration of the ambient state
type and no choice of an equivalence is used by the evaluator. -/


theorem listedBandCoordinates_nodup {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) : (listedBandCoordinates band).Nodup :=
  List.nodup_dedup _

theorem listedBandCoordinates_toFinset {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).toFinset = bandCoordinates band.toFinset := by
  ext coordinate
  constructor
  · intro hc
    obtain ⟨action, ha, hc⟩ := List.mem_flatMap.mp
      (List.mem_dedup.mp (List.mem_toFinset.mp hc))
    obtain ⟨child, hchild⟩ := List.mem_ofFn.mp hc
    rw [← hchild]
    exact action_coordinate_mem band.toFinset (List.mem_toFinset.mpr ha) child
  · intro hc
    obtain ⟨action, ha, hc⟩ := mem_biUnion.mp hc
    obtain ⟨child, _, heq⟩ := mem_image.mp hc
    apply List.mem_toFinset.mpr
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨action, List.mem_toFinset.mp ha, List.mem_ofFn.mpr ⟨child, heq⟩⟩

def listedBandCoordinateVector {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) : Vector (Fin M × σ) (listedBandCoordinates band).length :=
  Vector.ofFn (listedBandCoordinates band).get

theorem listedBandCoordinateVector_toList {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinateVector band).toList = listedBandCoordinates band := by
  simp only [listedBandCoordinateVector, Vector.toList_ofFn, List.ofFn_get]

theorem listedBandCoordinates_length {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).length = (bandCoordinates band.toFinset).card := by
  rw [← listedBandCoordinates_toFinset band,
    List.toFinset_card_of_nodup (listedBandCoordinates_nodup band)]

def materializedBandActionWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G j : ℕ) : Option (Fin M → σ) × ℕ :=
  let coordinates := listedBandCoordinateVector band
  let vertices := band.map fun action =>
    (action, restrictOptimizerVector coordinates (actionVector mass action))
  materializedSelectionWithWork vertices (restrictOptimizerVector coordinates linear) G j

/-- Materializing coordinates and vertices preserves the actual action
label selected by the complete finite optimizer, including all ties. -/
theorem materializedBandActionWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (hband : band ≠ []) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G j : ℕ) :
    (materializedBandActionWithWork band mass linear G j).1.getD (band.head hband) =
      finiteOptimizerAction band hband mass linear G j := by
  let coordinates := listedBandCoordinateVector band
  have hnodup : coordinates.toList.Nodup := by
    rw [show coordinates.toList = listedBandCoordinates band from
      listedBandCoordinateVector_toList band]
    exact listedBandCoordinates_nodup band
  have hcoordinates : coordinates.toList.toFinset = bandCoordinates band.toFinset := by
    rw [show coordinates.toList = listedBandCoordinates band from
      listedBandCoordinateVector_toList band, listedBandCoordinates_toFinset]
  have hvertexMaps :
      (((band.map fun action => (action, restrictOptimizerVector coordinates (actionVector mass action))).map
        Prod.snd).map Vector.get) =
      (band.map (actionVector mass)).map (fun v => fun i => v (coordinates.get i)) := by
    simp only [List.map_map]
    congr 1
    funext action i
    exact restrictOptimizerVector_get coordinates _ i
  have hlinear : (restrictOptimizerVector coordinates linear).get =
      fun i => linear (coordinates.get i) := by
    funext i
    exact restrictOptimizerVector_get coordinates linear i
  have hscore (action : Fin M → σ) :
      (∑ i : Fin (listedBandCoordinates band).length,
        rationalSmoothedGradient G (restrictOptimizerVector coordinates linear).get
          (finiteRationalOptimizer univ
            (((band.map fun action => (action, restrictOptimizerVector coordinates (actionVector mass action))).map
              Prod.snd).map Vector.get) (restrictOptimizerVector coordinates linear).get G j) i *
          (restrictOptimizerVector coordinates (actionVector mass action)).get i) =
        ∑ c ∈ bandCoordinates band.toFinset,
          rationalSmoothedGradient G linear
            (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass))
              linear G j) c * actionVector mass action c := by
    rw [hvertexMaps, hlinear, finiteRationalOptimizer_restrict coordinates hnodup]
    simp only [restrictOptimizerVector_get]
    change (∑ i, rationalSmoothedGradient G linear
      (finiteRationalOptimizer coordinates.toList.toFinset (band.map (actionVector mass)) linear G j)
      (coordinates.get i) * actionVector mass action (coordinates.get i)) = _
    have hs := coordinateVector_sum coordinates hnodup (fun c =>
      rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates.toList.toFinset (band.map (actionVector mass)) linear G j) c *
          actionVector mass action c)
    simpa only [hcoordinates] using hs
  unfold materializedBandActionWithWork
  rw [materializedSelectionWithWork_value, argmax_map_commutes]
  simp only [Function.comp_def, Option.map_map]
  rw [show (fun x : Fin M → σ => x) = id from rfl, Option.map_id]
  simp only [finiteOptimizerAction]
  apply congrArg (fun result : Option (Fin M → σ) => result.getD (band.head hband))
  apply congrArg (fun score : (Fin M → σ) → ℚ => band.argmax score)
  funext action
  exact hscore action

/-- Work of the optimizer after preparing its coordinate/vertex arrays.
The finite preparation loops are charged separately. -/
theorem materializedBandActionWithWork_optimizer_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G j : ℕ) (hj : j ≤ G ^ 80) :
    (materializedBandActionWithWork band mass linear G j).2 ≤
      (band.length + 1) * ((bandCoordinates band.toFinset).card + 1) * (G + 2) ^ 210 := by
  unfold materializedBandActionWithWork
  simpa only [List.length_map, listedBandCoordinates_length] using
    materializedSelectionWithWork_polynomial
      (band.map fun action => (action, restrictOptimizerVector
        (listedBandCoordinateVector band) (actionVector mass action)))
      (restrictOptimizerVector (listedBandCoordinateVector band) linear) G j hj

end EditApproximation

end OAI
