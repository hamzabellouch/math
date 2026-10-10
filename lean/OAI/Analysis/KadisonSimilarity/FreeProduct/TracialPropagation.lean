import OAI.Analysis.KadisonSimilarity.FreeProduct.PropagationTheorem
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteFullColumn
import OAI.Analysis.KadisonSimilarity.Constants

namespace OAI

/-! Propagation through actual left multipliers on a tracial Hilbert space.
The full-column approximation is derived from the concrete corner theorem;
the remaining hypotheses describe the repeated words and their tensor geometry. -/

noncomputable section
namespace KadisonSimilarity

universe u v wB wV wE wF

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : Type wB} {V : Type wV} {E : Type wE} {F : Type wF}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Y : H →L[ℂ] H} {B₀ : B →L[ℂ] B} {Bₖ : V →L[ℂ] V}
  {Q : Submodule ℂ H} [Q.HasOrthogonalProjection] {t : ℝ}

namespace RepeatedLetterWords

variable (D : RepeatedLetterWords (E := E) (F := F) Y B₀ Bₖ Q t)
  (G : TracialCornerGeometry P H)

/-- A word support represented by left multiplication commutes with every
right multiplier, directly from the tracial representation. -/
theorem tracial_support_commutes (q : P) (hsupport : D.support = G.left q) (b : P) :
    D.support.comp (G.right b) = (G.right b).comp D.support := by
  rw [hsupport]
  exact (G.right_left q b).symm

/-- The tracial left/right action law gives the letter commutation needed by
propagation. -/
theorem tracial_letter_commutes (x : ℕ → P)
    (hletter : ∀ n, D.letter n = G.left (x n)) (b : P) (n : ℕ) :
    (G.right b).comp (D.letter n) = (D.letter n).comp (G.right b) := by
  rw [hletter]
  exact G.right_left (x n) b

/-- Prefix multiplication obeys the same left/right action law. -/
theorem tracial_prefix_commutes (a : ℕ → P)
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n)) (b : P) (n : ℕ) :
    (G.right b).comp (D.wordPrefix n) = (D.wordPrefix n).comp (G.right b) := by
  rw [hprefix]
  exact G.right_left (a n) b

/-- An actual left letter preserves the complete right-supported column. -/
theorem tracial_letter_mem (r : P) (x : ℕ → P)
    (hletter : ∀ n, D.letter n = G.left (x n)) (n : ℕ) (z : H)
    (hz : z ∈ (G.corner 1 r).toSubmodule) :
    D.letter n z ∈ (G.corner 1 r).toSubmodule := by
  rw [hletter]
  exact G.rightColumn_mem r (x n) z hz

/-- An actual left prefix preserves the same column. -/
theorem tracial_prefix_mem (r : P) (a : ℕ → P)
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n)) (n : ℕ) (z : H)
    (hz : z ∈ (G.corner 1 r).toSubmodule) :
    D.wordPrefix n z ∈ (G.corner 1 r).toSubmodule := by
  rw [hprefix]
  exact G.rightColumn_mem r (a n) z hz

/-- An algebraic right support gives membership in the completed right
column. This allows the support projection to be chosen for each bounded
input vector separately. -/
theorem small_mem_tracial_column (r z : P) (v : B)
    (hsmall : D.small v = G.vector z) (hz : z * r = z) :
    D.small v ∈ (G.corner 1 r).toSubmodule := by
  change D.small v ∈ G.corner 1 r
  rw [G.mem_corner, hsmall]
  exact ⟨by simp, by simp only [G.right_vector, hz]⟩

/-- The concrete tracial action discharges all multiplier commutation and
column-preservation hypotheses in the abstract propagation theorem. -/
theorem propagation_of_tracial_column (ht : 0 < t)
    (q r : P) (x a : ℕ → P)
    (hsupport : D.support = G.left q)
    (hletter : ∀ n, D.letter n = G.left (x n))
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n))
    (b : P) {η : ℝ}
    (hcolumn : ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : B) (hv : D.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  exact D.propagation_of_column ht (G.corner 1 r).toSubmodule (G.right b) hcolumn
    (D.tracial_support_commutes G q hsupport b)
    (D.tracial_letter_commutes G x hletter b)
    (D.tracial_prefix_commutes G a hprefix b)
    (D.tracial_letter_mem G r x hletter)
    (D.tracial_prefix_mem G r a hprefix) v hv

/-- Supply a concrete supported full-column multiplier; no commutation or
invariance assumptions about that multiplier remain. -/
theorem propagation_of_tracial_full_column (ht : 0 < t)
    (q r : P) (x a : ℕ → P)
    (hsupport : D.support = G.left q)
    (hletter : ∀ n, D.letter n = G.left (x n))
    (hprefix : ∀ n, D.wordPrefix n = G.left (a n))
    {η : ℝ} (fullColumn : ∃ b : P, r * b = b ∧
      ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : B) (hv : D.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  obtain ⟨b, _, hcolumn⟩ := fullColumn
  exact D.propagation_of_tracial_column G ht q r x a hsupport hletter hprefix b hcolumn v hv

end RepeatedLetterWords

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

/-- Concrete tracial propagation with the manuscript constant. The column
estimate is proved by `full_column` from projection comparison and the cited
cyclic inputs, and is not an additional input. -/
theorem repeated_propagation_of_full_column
    (e : P) (he : IsStarProjection e) (r : P)
    (hfaithful : Function.Injective G.vector)
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → P)
    (hframe : ∀ i j, star (frame i) * frame j = if i = j then e else 0)
    (hsum : ∑ i, frame i * star (frame i) = 1)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYframe : ∀ i, Y.comp (G.left (frame i)) = (G.left (frame i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (D : RepeatedLetterWords (E := E) (F := F) Y B₀ Bₖ Q t) (ht : 0 < t)
    (q : P) (x a : ℕ → P)
    (hsupport : D.support = G.left q)
    (hletter : ∀ j, D.letter j = G.left (x j))
    (hprefix : ∀ j, D.wordPrefix j = G.left (a j))
    (v : B) (hv : D.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (D.repeatVector v) - D.repeatVector (B₀ v)‖ ≤
      2 * cyclicConstant * ε * ‖v‖ := by
  have hcolumn := G.full_column e he r hfaithful τ comparison hr hτ hn frame hframe
    hsum Y hYe hYframe hε hY published commutation
  have hbound := D.propagation_of_tracial_full_column G ht q r x a hsupport hletter
    hprefix hcolumn v hv
  simpa only [cyclicConstant, rowConstant, mul_assoc] using hbound

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
