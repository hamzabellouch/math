import OAI.Algebra.Universal.Congruence
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace OAI

/-!
# Graph characterization of finite congruence lattices

A finite lattice is the full congruence lattice of a nonempty finite algebra if and only if
it admits a finite nonempty lattice-colored graph satisfying `IsGraphWitness`. Principal
congruences supply the colors in one direction; all label-decreasing self-maps supply the
unary operations in the other.
-/

namespace FiniteCongruence

/-- A label-decreasing self-map; collapsed edges are permitted. -/
def Admissible {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (placement : Carrier → Carrier) : Prop :=
  ∀ left right, color (placement left) (placement right) ≤ color left right

/-- An oriented image of a seed edge under an admissible map. -/
def Marked {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  ∃ placement : Carrier → Carrier, Admissible color placement ∧
    ∃ edge ∈ seeds, placement edge.1 = left ∧ placement edge.2 = right

/-- Finite paths in the undirected marked graph, including paths of length zero. -/
def Connected {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  Relation.EqvGen (Marked color seeds) left right

/-- Symmetric colors separate vertices, satisfy the join triangle inequality, detect order,
and connect every pair below the join of any nonempty finite set of seed colors. -/
def IsGraphWitness {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat]
    (color : Carrier → Carrier → Lat) : Prop :=
  (∀ left right, color left right = color right left) ∧
  (∀ left right, color left right = ⊥ ↔ left = right) ∧
  (∀ left right middle, color left right ≤ color left middle ⊔ color middle right) ∧
  (∀ lower upper : Lat, ¬ lower ≤ upper →
    ∃ left right, color left right ≤ lower ∧ ¬ color left right ≤ upper) ∧
  (∀ seeds : Finset (Carrier × Carrier), seeds.Nonempty → ∀ left right,
    color left right ≤ seeds.sup (fun edge => color edge.1 edge.2) →
      Connected color seeds left right)

/-- The graph size is unbounded, but each individual witness is finite and nonempty. -/
def HasGraphWitness (Lat : Type) [Lattice Lat] [OrderBot Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ color : Fin size → Fin size → Lat, IsGraphWitness color

section PrincipalColors

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] {alg : Algebra Carrier}

/-- Color a pair by its principal congruence, transported to the lattice. -/
noncomputable def principalColor (equiv : Lat ≃o Congruence alg) (left right : Carrier) : Lat :=
  equiv.symm (Congruence.principal alg left right)

omit [OrderBot Lat] in
theorem principalColor_le (equiv : Lat ≃o Congruence alg) {left right : Carrier} {bound : Lat} :
    principalColor equiv left right ≤ bound ↔ equiv bound left right := by
  change equiv.symm (Congruence.principal alg left right) ≤ bound ↔ _
  rw [equiv.symm_apply_le]
  exact Congruence.principal_le

theorem map_bot_equality (equiv : Lat ≃o Congruence alg) :
    equiv ⊥ = Congruence.equality alg := by
  apply le_antisymm
  · have : (⊥ : Lat) ≤ equiv.symm (Congruence.equality alg) := bot_le
    simpa using equiv.monotone this
  · exact Congruence.equality_le _

theorem principalColor_eq_bot (equiv : Lat ≃o Congruence alg) (left right : Carrier) :
    principalColor equiv left right = ⊥ ↔ left = right := by
  rw [← le_bot_iff, principalColor_le, map_bot_equality, Congruence.equality_apply]

omit [OrderBot Lat] in
theorem principalColor_triangle (equiv : Lat ≃o Congruence alg) (left right middle : Carrier) :
    principalColor equiv left right ≤
      principalColor equiv left middle ⊔ principalColor equiv middle right := by
  apply (principalColor_le equiv).mpr
  apply (equiv _).trans
  · exact (principalColor_le equiv).mp le_sup_left
  · exact (principalColor_le equiv).mp le_sup_right

omit [OrderBot Lat] in
theorem principalColor_reflect (equiv : Lat ≃o Congruence alg) (lower upper : Lat)
    (notBelow : ¬ lower ≤ upper) :
    ∃ left right, principalColor equiv left right ≤ lower ∧
      ¬ principalColor equiv left right ≤ upper := by
  classical
  by_contra noPair
  apply notBelow
  apply equiv.le_iff_le.mp
  intro left right related
  by_contra notRelated
  exact noPair ⟨left, right, (principalColor_le equiv).mpr related,
    by simpa [principalColor_le] using notRelated⟩

end PrincipalColors

theorem admissible_id {Lat Carrier : Type} [Preorder Lat] (color : Carrier → Carrier → Lat) :
    Admissible color id := fun _ _ => le_rfl

theorem Admissible.comp {Lat Carrier : Type} [Preorder Lat]
    {color : Carrier → Carrier → Lat} {outer inner : Carrier → Carrier}
    (outerAdmissible : Admissible color outer) (innerAdmissible : Admissible color inner) :
    Admissible color (outer ∘ inner) :=
  fun left right => le_trans (outerAdmissible _ _) (innerAdmissible left right)

theorem marked_map {Lat Carrier : Type} [Preorder Lat] {color : Carrier → Carrier → Lat}
    {seeds : Finset (Carrier × Carrier)} {placement : Carrier → Carrier}
    (admissible : Admissible color placement) {left right : Carrier}
    (marked : Marked color seeds left right) :
    Marked color seeds (placement left) (placement right) := by
  rcases marked with ⟨inner, innerAdmissible, edge, member, rfl, rfl⟩
  exact ⟨placement ∘ inner, admissible.comp innerAdmissible, edge, member, rfl, rfl⟩

theorem connected_map {Lat Carrier : Type} [Preorder Lat] {color : Carrier → Carrier → Lat}
    {seeds : Finset (Carrier × Carrier)} {placement : Carrier → Carrier}
    (admissible : Admissible color placement) {left right : Carrier}
    (connected : Connected color seeds left right) :
    Connected color seeds (placement left) (placement right) := by
  induction connected with
  | rel left right marked => exact Relation.EqvGen.rel _ _ (marked_map admissible marked)
  | refl point => exact Relation.EqvGen.refl _
  | symm left right _ inductionHyp => exact Relation.EqvGen.symm _ _ inductionHyp
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

section Forward

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] {alg : Algebra Carrier}

omit [OrderBot Lat] in
theorem translation_admissible (equiv : Lat ≃o Congruence alg) (index : Fin alg.numOps)
    (coord : Fin (alg.arity index)) (inputs : Fin (alg.arity index) → Carrier) :
    Admissible (principalColor equiv) (translation alg index coord inputs) := by
  intro left right
  apply (principalColor_le equiv).mpr
  exact translation_preserves (equiv (principalColor equiv left right)) index coord inputs
    ((principalColor_le equiv).mp le_rfl)

/-- Connectivity in the marked graph is a congruence of the original algebra, not just
of its admissible unary maps. -/
noncomputable def pathCongruence (equiv : Lat ≃o Congruence alg)
    (seeds : Finset (Carrier × Carrier)) : Congruence alg :=
  ⟨Relation.EqvGen.setoid (Marked (principalColor equiv) seeds), by
    apply (compatible_iff_translations alg _).mpr
    intro index coord inputs left right related
    exact connected_map (translation_admissible equiv index coord inputs) related⟩

theorem principalColor_connected (equiv : Lat ≃o Congruence alg)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier)
    (below : principalColor equiv left right ≤
      seeds.sup (fun edge => principalColor equiv edge.1 edge.2)) :
    Connected (principalColor equiv) seeds left right := by
  have supBelow : seeds.sup (fun edge => principalColor equiv edge.1 edge.2) ≤
      equiv.symm (pathCongruence equiv seeds) := by
    apply Finset.sup_le
    intro edge member
    change equiv.symm (Congruence.principal alg edge.1 edge.2) ≤
      equiv.symm (pathCongruence equiv seeds)
    apply equiv.symm.monotone
    apply Congruence.principal_le.mpr
    exact Relation.EqvGen.rel _ _ ⟨id, admissible_id _, edge, member, rfl, rfl⟩
  have principalBelow : Congruence.principal alg left right ≤ pathCongruence equiv seeds :=
    equiv.symm.le_iff_le.mp (below.trans supBelow)
  exact Congruence.principal_le.mp principalBelow

theorem principalColor_isGraphWitness (equiv : Lat ≃o Congruence alg) :
    IsGraphWitness (principalColor equiv) := by
  refine ⟨?_, principalColor_eq_bot equiv, principalColor_triangle equiv,
    principalColor_reflect equiv, ?_⟩
  · intro left right
    simp only [principalColor, Congruence.principal_comm left right]
  · intro seeds _ left right below
    exact principalColor_connected equiv seeds left right below

end Forward

section Backward

variable {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat] [Fintype Carrier]

/-- All label-decreasing maps, made into a finite list of unary total operations. -/
noncomputable def graphAlgebra (color : Carrier → Carrier → Lat) : Algebra Carrier := by
  classical
  let Maps := {placement : Carrier → Carrier // Admissible color placement}
  exact {
    numOps := Fintype.card Maps
    arity := fun _ => 1
    op := fun index inputs => ((Fintype.equivFin Maps).symm index).1 (inputs 0)
  }

omit [OrderBot Lat] in
/-- Every admissible map is one of the basic unary operations. -/
theorem graphAlgebra_preserves (color : Carrier → Carrier → Lat)
    (rel : Congruence (graphAlgebra color)) {placement : Carrier → Carrier}
    (admissible : Admissible color placement) {left right : Carrier} (related : rel left right) :
    rel (placement left) (placement right) := by
  classical
  let Maps := {placement : Carrier → Carrier // Admissible color placement}
  have preserved := rel.compatible ((Fintype.equivFin Maps) ⟨placement, admissible⟩)
    (fun _ => left) (fun _ => right) (fun _ => related)
  simpa only [graphAlgebra, Maps, Equiv.symm_apply_apply] using preserved

/-- Each lattice element defines the equivalence relation of edges below its color. -/
noncomputable def labelCongruence (color : Carrier → Carrier → Lat)
    (witness : IsGraphWitness color) (bound : Lat) : Congruence (graphAlgebra color) := by
  classical
  refine ⟨⟨fun left right => color left right ≤ bound, ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · intro point
    rw [(witness.2.1 point point).mpr rfl]
    exact bot_le
  · intro left right below
    rwa [witness.1 right left]
  · intro left middle right first second
    exact (witness.2.2.1 left right middle).trans (sup_le first second)
  · intro index left right below
    exact ((((Fintype.equivFin
      {placement : Carrier → Carrier // Admissible color placement}).symm index).2) _ _).trans
        (below ⟨0, by change 0 < 1; decide⟩)

@[simp] theorem labelCongruence_apply (color : Carrier → Carrier → Lat)
    (witness : IsGraphWitness color) (bound : Lat) (left right : Carrier) :
    labelCongruence color witness bound left right ↔ color left right ≤ bound := Iff.rfl

theorem labelCongruence_le_iff (color : Carrier → Carrier → Lat)
    (witness : IsGraphWitness color) (lower upper : Lat) :
    labelCongruence color witness lower ≤ labelCongruence color witness upper ↔ lower ≤ upper := by
  constructor
  · intro below
    by_contra notBelow
    obtain ⟨left, right, belowLower, notBelowUpper⟩ := witness.2.2.2.1 lower upper notBelow
    exact notBelowUpper (below belowLower)
  · intro below left right belowLower
    exact belowLower.trans below

omit [OrderBot Lat] in
/-- Equivalence closure of marked edges lies in every congruence containing the seed edges. -/
theorem connected_below_congruence (color : Carrier → Carrier → Lat)
    (rel : Congruence (graphAlgebra color)) (seeds : Finset (Carrier × Carrier))
    (contains : ∀ edge ∈ seeds, rel edge.1 edge.2) {left right : Carrier}
    (connected : Connected color seeds left right) : rel left right := by
  induction connected with
  | rel left right marked =>
    obtain ⟨placement, admissible, edge, member, rfl, rfl⟩ := marked
    exact graphAlgebra_preserves color rel admissible (contains edge member)
  | refl point => exact rel.refl point
  | symm left right _ inductionHyp => exact rel.symm inductionHyp
  | trans left middle right _ _ first second => exact rel.trans first second

/-- Every congruence is recovered using all its related pairs. -/
theorem labelCongruence_surjective [Nonempty Carrier] (color : Carrier → Carrier → Lat)
    (witness : IsGraphWitness color) : Function.Surjective (labelCongruence color witness) := by
  classical
  intro rel
  let seeds : Finset (Carrier × Carrier) := Finset.univ.filter (fun edge => rel edge.1 edge.2)
  have membership : ∀ edge, edge ∈ seeds ↔ rel edge.1 edge.2 := by simp [seeds]
  have nonempty : seeds.Nonempty := by
    obtain ⟨point⟩ := ‹Nonempty Carrier›
    exact ⟨(point, point), (membership _).mpr (rel.refl point)⟩
  refine ⟨seeds.sup (fun edge => color edge.1 edge.2), ?_⟩
  apply Congruence.ext
  intro left right
  constructor
  · intro below
    exact connected_below_congruence color rel seeds (fun edge member => (membership edge).mp member)
      (witness.2.2.2.2 seeds nonempty left right below)
  · intro related
    change color left right ≤ seeds.sup (fun edge => color edge.1 edge.2)
    exact Finset.le_sup (f := fun edge : Carrier × Carrier => color edge.1 edge.2)
      ((membership (left, right)).mpr related)

/-- The lattice is isomorphic to the full congruence lattice of the graph algebra. -/
noncomputable def graphOrderIso [Nonempty Carrier] (color : Carrier → Carrier → Lat)
    (witness : IsGraphWitness color) : Lat ≃o Congruence (graphAlgebra color) :=
  { Equiv.ofBijective (labelCongruence color witness)
      ⟨fun lower upper equal => le_antisymm
        ((labelCongruence_le_iff color witness lower upper).mp equal.le)
        ((labelCongruence_le_iff color witness upper lower).mp equal.ge),
        labelCongruence_surjective color witness⟩ with
    map_rel_iff' := fun {lower upper} => labelCongruence_le_iff color witness lower upper }

end Backward

/-- A finite lattice is representable as the full congruence lattice of a nonempty finite
algebra exactly when it has a finite nonempty colored-graph witness. -/
theorem graph_criterion (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] :
    Representable Lat ↔ HasGraphWitness Lat := by
  constructor
  · rintro ⟨size, positive, alg, ⟨equiv⟩⟩
    exact ⟨size, positive, principalColor equiv, principalColor_isGraphWitness equiv⟩
  · rintro ⟨size, positive, color, witness⟩
    have : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    exact ⟨size, positive, graphAlgebra color, ⟨graphOrderIso color witness⟩⟩

end FiniteCongruence

end OAI
