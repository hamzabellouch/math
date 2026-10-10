import OAI.Analysis.Kaplansky.Products
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.NhdsWithin

namespace OAI

/-! Star-word polynomials and matrix polynomial density in the generated algebra. -/

noncomputable section
open scoped BigOperators Pointwise
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

def algebraStarLetter (x : Fin N → A) (l : Bool × Fin N) : A :=
  if l.1 then star (x l.2) else x l.2

def algebraStarWord (x : Fin N → A) (w : List (Bool × Fin N)) : A :=
  (w.map (algebraStarLetter x)).prod

@[simp] theorem algebraStarWord_append (x : Fin N → A) (u v : List (Bool × Fin N)) :
    algebraStarWord x (u++v)=algebraStarWord x u * algebraStarWord x v := by
  simp [algebraStarWord]

def starWordMonoid (x : Fin N → A) : Submonoid A where
  carrier := Set.range (algebraStarWord x)
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
    exact ⟨u++v,algebraStarWord_append x u v⟩

theorem starWordMonoid_eq_closure (x : Fin N → A) :
    starWordMonoid x = Submonoid.closure (Set.range x ∪ star (Set.range x)) := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons l w ih =>
      apply Submonoid.mul_mem _ _ ih
      apply Submonoid.subset_closure
      obtain ⟨b,i⟩ := l
      cases b with
      | false => exact Or.inl ⟨i,rfl⟩
      | true =>
        apply Or.inr
        simp [algebraStarLetter]
  · apply Submonoid.closure_le.mpr
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i,rfl⟩ := hz
      exact ⟨[(false,i)],by simp [algebraStarWord,algebraStarLetter]⟩
    · have hz' : star z ∈ Set.range x := by simpa using hz
      obtain ⟨i,hi⟩ := hz'
      exact ⟨[(true,i)],by simpa [algebraStarWord,algebraStarLetter] using congrArg star hi⟩

theorem starAdjoin_eq_wordSpan (x : Fin N → A) :
    (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (algebraStarWord x)) := by
  rw [StarAlgebra.adjoin_eq_span,← starWordMonoid_eq_closure]
  rfl

abbrev StarWordPolynomial (N : ℕ) := List (Bool × Fin N) →₀ ℂ

def evalStarWordPolynomial (x : Fin N → A) (p : StarWordPolynomial N) : A :=
  Finsupp.linearCombination ℂ (algebraStarWord x) p

/-- Every element of the actual algebraic star-adjoin is a finite sum of
explicit generator/adjoint words; this includes scalar constants. -/
theorem starAdjoin_exists_wordPolynomial (x : Fin N → A) {z : A}
    (hz : z ∈ StarAlgebra.adjoin ℂ (Set.range x)) :
    ∃ p : StarWordPolynomial N, evalStarWordPolynomial x p=z := by
  change z ∈ (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule at hz
  rw [starAdjoin_eq_wordSpan,← Finsupp.range_linearCombination] at hz
  exact hz

/-- Norm approximation in the actual closed generated algebra by a
finite star polynomial. No density hypothesis is supplied by the caller. -/
theorem generated_exists_wordPolynomial (x : Fin N → A) (z : generatedAlgebra (Set.range x))
    {ε : ℝ} (hε : 0<ε) :
    ∃ p : StarWordPolynomial N, ‖evalStarWordPolynomial x p - (z : A)‖ < ε := by
  have hz : (z : A) ∈ closure (StarAlgebra.adjoin ℂ (Set.range x) : Set A) := z.property
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨p,rfl⟩ := starAdjoin_exists_wordPolynomial x hw
  refine ⟨p,?_⟩
  simpa only [dist_eq_norm,norm_sub_rev] using hd

end Kaplansky

end

noncomputable section
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

theorem evalStarWordPolynomial_mem (x : Fin N → A) (p : StarWordPolynomial N) :
    evalStarWordPolynomial x p ∈ StarAlgebra.adjoin ℂ (Set.range x) := by
  change evalStarWordPolynomial x p ∈ (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule
  rw [starAdjoin_eq_wordSpan,← Finsupp.range_linearCombination]
  exact ⟨p,rfl⟩

def generatedWordPolynomial (x : Fin N → A) (p : StarWordPolynomial N) :
    generatedAlgebra (Set.range x) :=
  ⟨evalStarWordPolynomial x p,StarSubalgebra.le_topologicalClosure _ (evalStarWordPolynomial_mem x p)⟩

theorem generatedWordPolynomial_dense (x : Fin N → A) : DenseRange (generatedWordPolynomial x) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨p,hp⟩ := generated_exists_wordPolynomial x z hε
  refine ⟨p,?_⟩
  rw [Subtype.dist_eq,dist_eq_norm]
  change ‖(z : A)-evalStarWordPolynomial x p‖ < ε
  simpa only [norm_sub_rev] using hp

/-- Arbitrary rectangular matrices over the actual generated algebra have
finite star-polynomial approximants in their C*-matrix operator norm. -/
theorem generated_matrix_polynomial_approximation (x : Fin N → A)
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : CStarMatrix m n (generatedAlgebra (Set.range x))) {ε : ℝ} (hε : 0<ε) :
    ∃ p : m → n → StarWordPolynomial N,
      ‖CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j)) - W‖ < ε := by
  have hd : DenseRange (fun p : m → n → StarWordPolynomial N =>
      CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => generatedWordPolynomial_dense x))
  obtain ⟨p,hp⟩ := Metric.denseRange_iff.mp hd W ε hε
  exact ⟨p,by simpa only [dist_eq_norm,norm_sub_rev] using hp⟩

end Kaplansky

end

end OAI
