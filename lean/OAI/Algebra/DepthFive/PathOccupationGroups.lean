import OAI.Algebra.DepthFive.FockPaths
import OAI.Algebra.DepthFive.ImmOperatorPaths

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [DecidableEq σ]

/-- Coordinates of one path belonging to a fixed Boolean variable group,
viewed in that group's own coordinate type. -/
def selectedPathCoordinates (side : σ → Bool) (p : List σ) (b : Bool) :
    Finset {x // side x = b} :=
  p.toFinset.subtype (fun x => side x = b)

@[simp] theorem mem_selectedPathCoordinates (side : σ → Bool) (p : List σ)
    (b : Bool) (x : {x // side x = b}) :
    x ∈ selectedPathCoordinates side p b ↔ x.val ∈ p := by
  simp [selectedPathCoordinates]

theorem card_selectedPathCoordinates (side : σ → Bool) (p : List σ)
    (hp : p.Nodup) (b : Bool) :
    (selectedPathCoordinates side p b).card =
      (p.filter (fun x => side x == b)).length := by
  rw [selectedPathCoordinates, Finset.card_subtype]
  have hf : p.toFinset.filter (fun x => side x = b) =
      (p.filter (fun x => side x == b)).toFinset := by
    ext x
    simp
  rw [hf]
  exact List.toFinset_card_of_nodup (hp.filter _)

/-- Partitioning a squarefree path product into its two coordinate groups. -/
theorem path_product_split {R : Type*} [CommMonoid R]
    (side : σ → Bool) (p : List σ) (hp : p.Nodup) (f g : σ → R) :
    (p.map (fun x => if side x then f x else g x)).prod =
      (∏ x ∈ selectedPathCoordinates side p true, f x.val) *
        ∏ x ∈ selectedPathCoordinates side p false, g x.val := by
  rw [← List.prod_toFinset _ hp]
  simp only [selectedPathCoordinates, Finset.prod_subtype_eq_prod_filter]
  rw [← Finset.prod_filter_mul_prod_filter_not p.toFinset
    (fun x => side x = true) (fun x => if side x then f x else g x)]
  congr 1
  · apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]
  · have hf : p.toFinset.filter (fun x => ¬side x = true) =
        p.toFinset.filter (fun x => side x = false) := by
      ext x
      simp
    rw [hf]
    apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]

/-- The squared Fock amplitude is exactly the product of the derivative
occupations and successor multiplication occupations, on disjoint group types. -/
theorem pathAmplitude_sq_split [Fintype σ] (side : σ → Bool)
    (p : List σ) (hp : p.Nodup) (d : σ →₀ ℕ) :
    ((p.map (occupationAmplitude side d)).prod) ^ 2 =
      (∏ x ∈ selectedPathCoordinates side p true, (d x.val : ℝ)) *
        ∏ x ∈ selectedPathCoordinates side p false, ((d x.val : ℝ) + 1) := by
  rw [pathAmplitude_sq]
  exact path_product_split side p hp _ _

/-- Selecting coordinates from a path selects exactly the same number as
selecting its layer labels. -/
theorem card_selectedPathCoordinates_of_labels {ι : Type*} [DecidableEq ι]
    (side : σ → Bool) (labels : List σ) (p : List (σ × ι × ι))
    (hlabels : p.map Prod.fst = labels) (hnodup : labels.Nodup) (b : Bool) :
    (selectedPathCoordinates (fun x : σ × ι × ι => side x.1) p b).card =
      (labels.filter (fun x => side x == b)).length := by
  have hp : p.Nodup := List.Nodup.of_map Prod.fst (hlabels ▸ hnodup)
  rw [card_selectedPathCoordinates _ _ hp]
  rw [← hlabels, List.filter_map, List.length_map]
  rfl

/-- Every actual IMM path selects one coordinate in each selected layer,
including when the ambient layer has inactive endpoint coordinates. -/
theorem immPath_selectedCoordinates_card (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n hn) (b : Bool) :
    (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1) p b).card =
      (Finset.univ.filter (fun t : Fin n => side t = b)).card := by
  rw [card_selectedPathCoordinates_of_labels side (List.finRange n) p
    (immPaths_labels n hn p hp) (List.nodup_finRange n)]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter
    (fun x => side x == b))]
  congr 1
  ext x
  simp

/-- Concrete IMM first-trace path mass in the two independent occupation groups. -/
theorem immPathAmplitude_sq_split (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n hn) (d : (Fin n × Fin n × Fin n) →₀ ℕ) :
    ((p.map (occupationAmplitude (fun x => side x.1) d)).prod) ^ 2 =
      (∏ x ∈ selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
        p true, (d x.val : ℝ)) *
      ∏ x ∈ selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
        p false, ((d x.val : ℝ) + 1) :=
  pathAmplitude_sq_split _ p (immPaths_nodup n hn p hp) d

/-- Complement-fiber version, aligned with `bidegreeExponentsEquiv`. -/
def complementaryPathCoordinates (side : σ → Bool) (p : List σ) :
    Finset {x // ¬side x = true} :=
  p.toFinset.subtype (fun x => ¬side x = true)

@[simp] theorem mem_complementaryPathCoordinates (side : σ → Bool) (p : List σ)
    (x : {x // ¬side x = true}) :
    x ∈ complementaryPathCoordinates side p ↔ x.val ∈ p := by
  simp [complementaryPathCoordinates]

theorem path_product_split_complement {R : Type*} [CommMonoid R]
    (side : σ → Bool) (p : List σ) (hp : p.Nodup) (f g : σ → R) :
    (p.map (fun x => if side x then f x else g x)).prod =
      (∏ x ∈ selectedPathCoordinates side p true, f x.val) *
        ∏ x ∈ complementaryPathCoordinates side p, g x.val := by
  rw [← List.prod_toFinset _ hp]
  simp only [selectedPathCoordinates, complementaryPathCoordinates,
    Finset.prod_subtype_eq_prod_filter]
  rw [← Finset.prod_filter_mul_prod_filter_not p.toFinset
    (fun x => side x = true) (fun x => if side x then f x else g x)]
  congr 1
  · apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]
  · apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]

theorem pathAmplitude_sq_split_complement [Fintype σ] (side : σ → Bool)
    (p : List σ) (hp : p.Nodup) (d : σ →₀ ℕ) :
    ((p.map (occupationAmplitude side d)).prod) ^ 2 =
      (∏ x ∈ selectedPathCoordinates side p true, (d x.val : ℝ)) *
        ∏ x ∈ complementaryPathCoordinates side p, ((d x.val : ℝ) + 1) := by
  rw [pathAmplitude_sq]
  exact path_product_split_complement side p hp _ _

theorem immPath_complementaryCoordinates_card (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n hn) :
    (complementaryPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1) p).card =
      (Finset.univ.filter (fun t : Fin n => ¬side t = true)).card := by
  simpa only [complementaryPathCoordinates, selectedPathCoordinates, Finset.card_subtype,
    Bool.not_eq_true]
    using immPath_selectedCoordinates_card n hn side p hp false

end Problem335

end

end OAI
