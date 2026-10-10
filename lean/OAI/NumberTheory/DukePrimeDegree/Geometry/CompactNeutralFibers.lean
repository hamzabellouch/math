import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralSubordinateObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralNameCovers

namespace OAI

/-! # Uniform finite covers of neutral itinerary fibers

The small displacement bound puts every bilateral fiber in one fixed
compact subset of the diagonal centralizer. Thus the number of reference
orbits needed for a given accuracy is independent of the base point and
the length of the observed orbit.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

local instance (n : ℕ) : MeasurableSpace (G n) := borel (G n)
local instance (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

def compactNeutralDisplacements {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    Set (G n) :=
  {g | (∀ i j, |g.val i j| ≤ 2) ∧
    ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)}

theorem isCompact_compactNeutralDisplacements {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    IsCompact (compactNeutralDisplacements ell hell) := by
  have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
      ∀ i j, |M i j| ≤ 2} := by
    have h : IsCompact ((Icc (-2 : ℝ) 2).matrix : Set (Matrix (Fin n) (Fin n) ℝ)) :=
      isCompact_Icc.matrix
    simpa only [Set.matrix,mem_Icc,abs_le] using h
  have hbound : IsCompact {g : G n | ∀ i j, |g.val i j| ≤ 2} :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hbox
  have hcomm : IsClosed {g : G n | ∀ t : ℝ,
      Commute g (diagonalOneParameter ell hell t)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro t
    exact isClosed_eq (continuous_id.mul continuous_const)
      (continuous_const.mul continuous_id)
  exact hbound.inter_right hcomm

theorem mem_compactNeutralDisplacements_of_small {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : g ∈ matrixBall n 1)
    (hc : ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) :
    g ∈ compactNeutralDisplacements ell hell := by
  refine ⟨?_,hc⟩
  intro i j
  have h := hg i j
  have he : |(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have ht := abs_add_le (g.val i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j)
    ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
  rw [sub_add_cancel] at ht
  linarith

/-- A bilateral fiber with a small neutral lift admits a fixed finite
list of reference orbits; its geometric coding cost does not grow in time. -/
theorem finite_neutral_itinerary_cover {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ)
    (hQ : ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → G n), ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ i, ∀ t : ℝ,
        quotientLogDistance (rightAction y (diagonalOneParameter ell hell t))
          (rightAction (rightAction x (v i)) (diagonalOneParameter ell hell t)) < ε := by
  let K := compactNeutralDisplacements ell hell
  obtain ⟨N,v,r,_,_,hcov⟩ := compact_neutral_measurable_selector ell hell K
    (isCompact_compactNeutralDisplacements ell hell) (fun g hg => hg.2) hε
  refine ⟨N,v,?_⟩
  intro x y hf hb
  obtain ⟨g,hg,hgx,hgc⟩ := hQ x y hf hb
  let k : K := ⟨g,mem_compactNeutralDisplacements_of_small ell hell g hg hgc⟩
  refine ⟨r k,?_⟩
  intro t
  simpa only [k,hgx] using hcov k x t

end DukePrimeDegree

end

end OAI
