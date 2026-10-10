import Mathlib

namespace OAI

/-!
# Bounded-degree coboundary expanders in every dimension

Finite connected pure complexes with uniformly bounded top-face incidence and
uniform weighted coboundary expansion over F₂ in all degrees below the dimension.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders

/-- A finite abstract simplicial complex with every labelled vertex present. -/
structure Complex where
  vertexCount : ℕ
  faces : Finset (Finset (Fin vertexCount))
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces
  vertex_mem : ∀ v, {v} ∈ faces

namespace Complex

/-- Faces of dimension `i` have exactly `i + 1` vertices. -/
def facesOf (X : Complex) (i : ℕ) : Finset (Finset (Fin X.vertexCount)) :=
  X.faces.filter (fun σ => σ.card = i + 1)

def Face (X : Complex) (i : ℕ) := {σ // σ ∈ X.facesOf i}

instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := Subtype.fintype _
instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := Classical.decEq _

/-- Exact purity: top faces exist and every face lies in a top face. -/
def Pure (X : Complex) (s : ℕ) : Prop :=
  (X.facesOf s).Nonempty ∧
  ∀ σ ∈ X.faces, ∃ τ ∈ X.facesOf s, σ ⊆ τ

/-- Connectedness of the nonempty one-skeleton. -/
def Connected (X : Complex) : Prop :=
  Nonempty (Fin X.vertexCount) ∧
  ∀ v w : Fin X.vertexCount,
    Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ X.faces) v w

abbrev Cochain (X : Complex) (i : ℕ) := X.Face i → ZMod 2

/-- Weights are normalized counts of incident top-dimensional faces. -/
def weight (X : Complex) (s i : ℕ) (σ : X.Face i) : ℝ :=
  (((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card : ℝ) /
    ((Nat.choose (s + 1) (i + 1) : ℝ) * (X.facesOf s).card)

/-- Weighted support norm. -/
def norm (X : Complex) (s i : ℕ) (f : X.Cochain i) : ℝ :=
  ∑ σ : X.Face i, if f σ ≠ 0 then X.weight s i σ else 0

/-- Simplicial coboundary over F₂. -/
def coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) : X.Cochain (i + 1) :=
  fun τ => ∑ σ : X.Face i, if σ.val ⊆ τ.val then f σ else 0

/-- Actual coboundaries, with constant cochains in degree zero. -/
def coboundaries (X : Complex) : (i : ℕ) → Set (X.Cochain i)
  | 0 => {f | ∃ c : ZMod 2, f = fun _ => c}
  | i + 1 => Set.range (X.coboundary i)

/-- Distance in the weighted support norm; on a nonempty finite set it is a minimum. -/
def distance (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) : ℝ :=
  sInf ((fun a => X.norm s i (f - a)) '' A)

/-- Number of top-dimensional faces incident to a vertex. -/
def topDegree (X : Complex) (s : ℕ) (v : Fin X.vertexCount) : ℕ :=
  ((X.facesOf s).filter (fun τ => v ∈ τ)).card

end Complex

/-- Both constants are uniform over the sequence, all degrees below `d`, and all cochains. -/
def MainStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ (D : ℕ) (ε : ℝ), 0 < ε ∧
      ∃ X : ℕ → Complex,
        (∀ m, (X m).Pure d ∧ (X m).Connected) ∧
        Tendsto (fun m => ((X m).facesOf 0).card) atTop atTop ∧
        (∀ m (v : Fin (X m).vertexCount), (X m).topDegree d v ≤ D) ∧
        ∀ m i, i < d → ∀ f : (X m).Cochain i,
          ε * (X m).distance d i f ((X m).coboundaries i) ≤
            (X m).norm d (i + 1) ((X m).coboundary i f)

theorem main : MainStatement := by
  sorry

end CoboundaryExpanders

end

end OAI
