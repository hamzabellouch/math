import Mathlib

namespace OAI

noncomputable section

namespace Problem313

abbrev GraphEdge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}

abbrev GraphConfig (n : ℕ) := GraphEdge n → Bool

def permEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (e : GraphEdge n) : GraphEdge n :=
  ⟨e.1.map π.toEmbedding, by simpa using e.2⟩

def permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : GraphConfig n :=
  fun e => x (permEdge π.symm e)

def VertexInvariant {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : GraphConfig n),
    f (permuteConfig π x) = f x

def ConfigLE {n : ℕ} (x y : GraphConfig n) : Prop :=
  ∀ e, x e = true → y e = true

def IncreasingGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ x y, ConfigLE x y → f x = true → f y = true

def NontrivialGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  (∃ x, f x = true) ∧ (∃ x, f x = false)

def boolReal (b : Bool) : ℝ :=
  match b with
  | false => 0
  | true => 1

def graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) : ℝ := by
  classical
  exact Finset.univ.prod (fun e : GraphEdge n =>
    if x e = true then p else 1 - p)

def graphMean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    graphWeight p x * boolReal (f x))

def graphQuantile {n : ℕ} (a : ℝ) (f : GraphConfig n → Bool) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ graphMean p f ≥ a}

theorem sharp_threshold_width :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  sorry

end Problem313

end

end OAI
