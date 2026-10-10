import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactNeutralFibers
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalNameCovers

namespace OAI

/-! # Measurable reference names on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measurable_choice_fin_on {Y : Type*} [MeasurableSpace Y]
    {M : ℕ} (i₀ : Fin M) (S : Fin M → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (E : Set Y) (hE : MeasurableSet E)
    (hcover : ∀ y ∈ E, ∃ i, y ∈ S i) :
    ∃ r : Y → Fin M, Measurable r ∧ ∀ y ∈ E, y ∈ S (r y) := by
  obtain ⟨r,hr,h⟩ := measurable_choice_fin_cover (fun i => S i ∪ Eᶜ)
    (fun i => (hS i).union hE.compl) (fun y => by
      by_cases hy : y ∈ E
      · obtain ⟨i,hi⟩ := hcover y hy
        exact ⟨i,Or.inl hi⟩
      · exact ⟨i₀,Or.inr hy⟩)
  refine ⟨r,hr,?_⟩
  intro y hy
  rcases h y with hi | hi
  · exact hi
  · exact (hi hy).elim

def bilateralNameFiber {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x : X n) : Set (X n) :=
  {y | (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
    ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)}

theorem measurableSet_bilateralNameFiber {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (x : X n) :
    MeasurableSet (bilateralNameFiber ell hell Q x) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  simp only [bilateralNameFiber,Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun k : ℕ =>
    measurableSet_eq_fun (hQ.comp ((hT (-1)).iterate k)) measurable_const).inter
      (MeasurableSet.iInter fun k : ℕ =>
        measurableSet_eq_fun (hQ.comp ((hT 1).iterate k)) measurable_const)

/-- Every finite time segment has a measurable reference label on the
fiber, using a list whose size is independent of the time segment. -/
theorem measurable_neutral_fiber_names {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (v : Fin M → G n), ∀ (N : ℕ) (x : X n),
      ∃ r : X n → Fin M, Measurable r ∧
        ∀ y ∈ bilateralNameFiber ell hell Q x, ∀ j : Fin N,
          quotientLogDistance
            (rightAction (rightAction x (v (r y)))
              (diagonalOneParameter ell hell (-(j.val:ℝ))))
            (rightAction y (diagonalOneParameter ell hell (-(j.val:ℝ)))) < ε := by
  obtain ⟨M,v,hcover⟩ := finite_neutral_itinerary_cover ell hell Q
    (fun x y hf hb => hlift x y ⟨hf,hb⟩) hε
  let x₀ : X n := Quotient.mk _ (1 : G n)
  obtain ⟨i₀,_⟩ := hcover x₀ x₀ (fun _ => rfl) (fun _ => rfl)
  refine ⟨M,v,?_⟩
  intro N x
  let S (i : Fin M) : Set (X n) := {y | ∀ j : Fin N,
    quotientLogDistance
      (rightAction (rightAction x (v i)) (diagonalOneParameter ell hell (-(j.val:ℝ))))
      (rightAction y (diagonalOneParameter ell hell (-(j.val:ℝ)))) < ε}
  have hS (i : Fin M) : MeasurableSet (S i) := by
    simp only [S,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (isOpen_lt ((continuous_quotientLogDistance n _).comp
      (continuous_rightAction _)) continuous_const).measurableSet
  obtain ⟨r,hr,hs⟩ := measurable_choice_fin_on i₀ S hS
    (bilateralNameFiber ell hell Q x) (measurableSet_bilateralNameFiber ell hell Q hQ x)
    (fun y hy => by
      obtain ⟨i,hi⟩ := hcover x y hy.1 hy.2
      refine ⟨i,fun j => ?_⟩
      rw [quotientLogDistance_symm]
      exact hi (-(j.val:ℝ)))
  exact ⟨r,hr,hs⟩

end DukePrimeDegree

end

end OAI
