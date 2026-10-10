import OAI.Combinatorics.Ryser.Construction.DirectionSets
import OAI.Combinatorics.Ryser.Construction.GadgetAlgebra
import OAI.Combinatorics.Ryser.Construction.Intersection

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k] [DecidableEq F] [DecidableEq G]

theorem projection_cubeMap_axis_eq_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection d (cubeMap p) = projection d (cubeMap q) ↔
      projection d p = projection d q := let _ := instDecidableEqk; by
  rcases hd with rfl | rfl
  · change p.1 ^ 3 = q.1 ^ 3 ↔ p.1 = q.1
    exact (cube_bijective hcop).injective.eq_iff
  · simp only [projection_some_zero, cubeMap]

theorem projection_placedPoint_cubeMap_axis_eq_iff
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
        projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d (cubeMap p) = projection d (cubeMap q) :=
  (projection_placedPoint_eq_iff σ M b d p q).trans
    (projection_cubeMap_axis_eq_iff hcop d hd p q).symm

theorem cubeMap_incidence_axis_of_placed_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0)
    (ell : AffineLine F) (hell : ell.1 = placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) :
    Incidence (cubeMap p) (lineThrough d (cubeMap q)) := by
  have hproj : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  rw [hell] at hproj
  exact (projection_placedPoint_cubeMap_axis_eq_iff σ M b hcop d hd p q).1 hproj

theorem placedPoint_eq_of_incidence_of_direction_outside
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ∀ d : Direction k, ell.1 ≠ placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := let _ := instFintypek; by
  let d := (joinLine p q).1
  have hsmall : projection d p = projection d q :=
    (incidence_joinLine_left p q).trans (incidence_joinLine_right p q).symm
  have hplaced := (projection_placedPoint_eq_iff σ M b d p q).2 hsmall
  have hell : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  apply placedPoint_injective σ M b
  exact point_eq_of_projection_eq_of_ne_direction (houtside d) hell hplaced

theorem placedPoint_eq_of_incidence_outside_altered_axis
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ell.1 ∉ alteredDirections σ M ∪ axisDirections σ M)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := by
  apply placedPoint_eq_of_incidence_of_direction_outside σ M b ell ?_ p q hp hq
  intro d hd
  apply houtside
  rw [hd]
  exact placedDirection_mem_altered_or_axis σ M d

def placedConfiguration (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (Y : Finset (Point k)) (X : Finset (Point F)) :
    ConfigurationData k F G where
  altered i := alteredDirections σ (M i)
  inverseSlope i := alteredInverseSlope σ (M i)
  base i := placedPoint σ (M i) (b i)
  transform := cubeMap
  retained := Y
  ordinaryPoints := X

variable [Fintype F]

theorem placedExceptionalEdge_inter_sameGroup
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (p q : Point k) :
    (exceptionalEdge (placedConfiguration σ M b Y X) i p ∩
      exceptionalEdge (placedConfiguration σ M b Y X) i q).Nonempty := by
  exact exceptionalEdge_inter_sameGroup (placedConfiguration σ M b Y X) i
    (placedDirection σ (M i))
    (placedDirection_mem_alteredDirections σ (M i))
    (inverseSlope_placedDirection σ (M i))
    (placedDirection_axis_notMem_alteredDirections σ (M i))
    (fun d hd w z hproj =>
      (projection_placedPoint_cubeMap_axis_eq_iff σ (M i) (b i)
        hcop d hd w z).2 hproj) p q

theorem placedExceptionalEdge_injective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (a c : k) (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c) :
    Function.Injective (exceptionalEdge (placedConfiguration σ M b Y X) i) := by
  have hinverse : alteredInverseSlope σ (M i)
      ⟨placedDirection σ (M i) (some a), placedDirection_mem_alteredDirections σ (M i) a ha⟩ ≠
      alteredInverseSlope σ (M i)
      ⟨placedDirection σ (M i) (some c), placedDirection_mem_alteredDirections σ (M i) c hc⟩ := by
    rw [inverseSlope_placedDirection σ (M i) a ha,
      inverseSlope_placedDirection σ (M i) c hc]
    exact hac
  exact exceptionalEdge_injective (placedConfiguration σ M b Y X) i
    (cubeMap_bijective hcop).injective
    ⟨placedDirection σ (M i) (some a), placedDirection_mem_alteredDirections σ (M i) a ha⟩
    ⟨placedDirection σ (M i) (some c), placedDirection_mem_alteredDirections σ (M i) c hc⟩
    hinverse

variable [Fintype G]

theorem placedHypergraph_intersecting
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (havoid : ∀ x ∈ X, ∀ i, ∀ w ∈ Y, ∀ d ∈ alteredDirections σ (M i),
      projection d x ≠ projection d (placedPoint σ (M i) (b i) w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ Y, ∀ z ∈ Y,
      ∀ d ∈ alteredDirections σ (M i),
        projection d (placedPoint σ (M i) (b i) w) ≠
          projection d (placedPoint σ (M j) (b j) z)) :
    Intersecting (hypergraph (placedConfiguration σ M b Y X)) := by
  exact hypergraph_intersecting_of_geometric_data (placedConfiguration σ M b Y X)
    (fun i => placedDirection σ (M i))
    (fun i => placedDirection_mem_alteredDirections σ (M i))
    (fun i => inverseSlope_placedDirection σ (M i))
    (fun i => placedDirection_axis_notMem_alteredDirections σ (M i))
    (fun i d hd p q hproj =>
      (projection_placedPoint_cubeMap_axis_eq_iff σ (M i) (b i)
        hcop d hd p q).2 hproj)
    havoid hseparate

end RyserCoveringCounterexample.Construction

end

end OAI
