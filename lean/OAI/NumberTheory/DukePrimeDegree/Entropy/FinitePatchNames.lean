import OAI.NumberTheory.DukePrimeDegree.Geometry.TerminalNeutralPairs

namespace OAI

/-! # Finite reference names on a finite union of neutral future patches -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem finite_patch_terminal_names {n p : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (E : Fin p → Set (X n)) (hE : ∀ i, MeasurableSet (E i))
    (hpair : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (N : ℕ) (s : ℕ → ℕ),
      ∃ (r : X n → Fin M) (v : Fin M → Fin N → X n), Measurable r ∧
      ∀ y, fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N y=s →
        ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[N] y) ∈ ⋃ i, E i →
        ∀ j : Fin N, quotientLogDistance (v (r y) j)
          ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[j.val] y) < ε := by
  classical
  let T := fun z : X n => rightAction z (diagonalOneParameter ell hell (-1))
  let K := compactNeutralDisplacements ell hell
  obtain ⟨m,v,c,_,_,hc⟩ := compact_neutral_measurable_selector ell hell K
    (isCompact_compactNeutralDisplacements ell hell) (fun g hg => hg.2) hε
  let e := (Fintype.equivFin (Option (Fin p × Fin m))).symm
  refine ⟨Fintype.card (Option (Fin p × Fin m)),?_⟩
  intro N s
  let F := fullFutureObservation T Q N
  let x₀ : X n := Quotient.mk _ (1 : G n)
  let x (i : Fin p) : X n :=
    if h : ∃ z, F z=s ∧ T^[N] z ∈ E i then h.choose else x₀
  let ref : Option (Fin p × Fin m) → Fin N → X n := fun a j =>
    match a with
    | none => x₀
    | some (i,k) => rightAction (rightAction (x i) (v k))
        (diagonalOneParameter ell hell (-(j.val:ℝ)))
  let S (a : Fin (Fintype.card (Option (Fin p × Fin m)))) : Set (X n) :=
    {y | ∀ j : Fin N, quotientLogDistance (ref (e a) j) (T^[j.val] y) < ε}
  have hS (a) : MeasurableSet (S a) := by
    simp only [S,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (isOpen_lt ((continuous_quotientLogDistance n _).comp
      ((continuous_rightAction _).iterate j.val)) continuous_const).measurableSet
  let A := {y | F y=s ∧ T^[N] y ∈ ⋃ i, E i}
  have hF : Measurable F := fullFutureObservation_measurable
    (continuous_rightAction _).measurable hQ N
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun hF measurable_const).inter
      ((MeasurableSet.iUnion hE).preimage ((continuous_rightAction _).measurable.iterate N))
  have hcover : ∀ y ∈ A, ∃ a, y ∈ S a := by
    intro y hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy.2
    have hex : ∃ z, F z=s ∧ T^[N] z ∈ E i := ⟨y,hy.1,hi⟩
    have hx : F (x i)=s ∧ T^[N] (x i) ∈ E i := by
      simpa only [x,dite_eq_left hex] using hex.choose_spec
    have hobs : fullFutureObservation T Q 0 (T^[N] (x i)) =
        fullFutureObservation T Q 0 (T^[N] y) := by
      rw [←fullFutureObservation_terminal ell hell Q N (x i),
        ←fullFutureObservation_terminal ell hell Q N y]
      exact hx.1.trans hy.1.symm
    obtain ⟨g,hg,hxy,hcomm⟩ := hpair i _ hx.2 _ hi hobs
    have hxy' := neutral_displacement_of_terminal ell hell N (x i) y g hcomm hxy
    let k : K := ⟨g,mem_compactNeutralDisplacements_of_small ell hell g hg hcomm⟩
    refine ⟨e.symm (some (i,c k)),?_⟩
    intro j
    rw [Equiv.apply_symm_apply]
    dsimp only [ref]
    rw [diagonal_negative_iterate,quotientLogDistance_symm]
    simpa only [k,hxy'] using hc k (x i) (-(j.val:ℝ))
  obtain ⟨r,hr,hsel⟩ := measurable_choice_fin_on (e.symm none) S hS A hA hcover
  exact ⟨r,(fun a => ref (e a)),hr,fun y hy hmem => hsel y ⟨hy,hmem⟩⟩

end DukePrimeDegree

end

end OAI
