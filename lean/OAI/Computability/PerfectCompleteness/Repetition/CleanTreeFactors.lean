import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedCardinality
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanTreeFactors

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open ProjectedCardinality FiniteProduct CleanConditioning

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Index (branch : Nat → Nat) (n calls : Nat) (rows : Nat → Nat) :=
  Fin calls ⊕ (Σ node : Nodes branch n, Fin (rows (Nodes.height node)))

def height (calls : Nat) (rows : Nat → Nat) : Index branch n calls rows → Nat
  | .inl _ => n
  | .inr p => Nodes.height p.1

def square (calls : Nat) (rows : Nat → Nat) : Index branch n calls rows → Bool
  | .inl _ => true
  | .inr _ => false

def factorIds (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    (j : Index branch n calls rows) → Slots branch (height calls rows j) → Fin t → Nat
  | .inl _, s, k => ids s k
  | .inr p, s, k => ids ((Nodes.path p.1).slotEmbedding s) k

abbrev Factors (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) (j : Index branch n calls rows) :=
  Factor (square calls rows j) (factorIds calls rows ids j)

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :=
  (Fin calls → squareSpace (H (projectedSlots ids))) × Arrays (projectedSlots ids) rows

instance rawFintype (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Fintype (Raw calls rows ids) :=
  Fintype.ofFinite _

def zeroRaw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Raw calls rows ids :=
  (fun _ => 0, fun _ _ => 0)

instance rawNonempty (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Nonempty (Raw calls rows ids) :=
  ⟨zeroRaw calls rows ids⟩

def rawEquiv (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    ((j : Index branch n calls rows) → Factors calls rows ids j) ≃ Raw calls rows ids where
  toFun x := (fun q => x (.inl q), fun node row => x (.inr ⟨node, row⟩))
  invFun x j := match j with
    | .inl q => x.1 q
    | .inr p => x.2 p.1 p.2
  left_inv x := by
    funext j
    cases j <;> rfl
  right_inv x := by
    cases x
    rfl

theorem rawEquiv_zero (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    rawEquiv calls rows ids
      (fun j => factorZero (square calls rows j) (factorIds calls rows ids j)) =
        zeroRaw calls rows ids := rfl

def rawLaw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : FiniteDistribution (Raw calls rows ids) :=
  (law (fun j : Index branch n calls rows =>
    FiniteDistribution.uniform (Factors calls rows ids j))).pushforward (rawEquiv calls rows ids)

theorem rawLaw_uniform (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    rawLaw calls rows ids = FiniteDistribution.uniform (Raw calls rows ids) := by
  unfold rawLaw
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card ((j : Index branch n calls rows) → Factors calls rows ids j) : ℝ) =
    1 / (Fintype.card (Raw calls rows ids) : ℝ)
  rw [Fintype.card_congr (rawEquiv calls rows ids)]

def allZero (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) (x : Raw calls rows ids) : Bool := by
  classical
  exact decide ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)

theorem allZero_rawEquiv (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat)
    (x : (j : Index branch n calls rows) → Factors calls rows ids j) :
    allZero calls rows ids (rawEquiv calls rows ids x) =
      allEvent (fun j y => decide (y = factorZero
        (square calls rows j) (factorIds calls rows ids j))) x := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [allZero, allEvent, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, ha⟩ j
    cases j with
    | inl q => exact hc q
    | inr p => exact ha p.1 p.2
  · intro h
    exact ⟨fun q => h (.inl q), fun node row => h (.inr ⟨node, row⟩)⟩

theorem probability_allZero (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    (rawLaw calls rows ids).probability (allZero calls rows ids) =
      ∏ j : Index branch n calls rows,
        1 / (shapeCardinality branch t (height calls rows) (square calls rows) j : ℝ) := by
  rw [rawLaw, FiniteDistribution.probability_pushforward]
  simp_rw [allZero_rawEquiv]
  rw [probability_law_all]
  apply Finset.prod_congr rfl
  intro j _
  rw [UniformLatent.probability_uniform_singleton]
  rw [factor_card_eq (square calls rows j) (factorIds calls rows ids j) (fun _ _ => 0)]
  rfl

theorem probability_allZero_pos (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    0 < (rawLaw calls rows ids).probability (allZero calls rows ids) := by
  rw [probability_allZero]
  exact shape_zero_probability_pos branch t (height calls rows) (square calls rows)

end
end PerfectCompleteness.CleanTreeFactors

end

end OAI
