import OAI.Probability.FreeIsing.Trees.ColoredPathAverage
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

namespace Problem367

theorem prefixFlip_reduced_cons {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) :
    prefixFlip c ⟨w, h.tail⟩ = ⟨c :: w, h⟩ := by
  apply Subtype.ext
  cases w with
  | nil => rfl
  | cons a w =>
    simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp h).1]

theorem prefixFlip_reduced_dropLast {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) (hw : w ≠ []) :
    prefixFlip c ⟨w.dropLast, h.tail.dropLast⟩ =
      ⟨(c :: w).dropLast, h.dropLast⟩ := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b w =>
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord,
        (List.isChain_cons_cons.mp h).1]

namespace ColoredPathAverage

def tailVertex {d n : ℕ} {i : Fin d} (p : Path d n i) : TreeVertex d :=
  ⟨(colors p).dropLast, (colors_isChain p).dropLast⟩

def headVertex {d n : ℕ} {i : Fin d} (p : Path d n i) : TreeVertex d :=
  ⟨colors p, colors_isChain p⟩

@[simp] theorem headVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    headVertex p = prefixFlip i (headVertex p.2) := by
  symm
  exact prefixFlip_reduced_cons i (colors p.2) (colors_isChain p)

@[simp] theorem tailVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    tailVertex p = prefixFlip i (tailVertex p.2) := by
  symm
  apply prefixFlip_reduced_dropLast i (colors p.2) (colors_isChain p)
  intro h
  have := colors_length p.2
  simp [h] at this

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem pathValue_eq_edgeVector {d : ℕ}
    (S : Fin d → E ≃ₗᵢ[𝕜] E) (A : TreeVertex d → TreeVertex d → E)
    (y : ColoredEdgeLifts.EdgeSpace d E)
    (hy : ∀ i, y i = A ⟨[], List.IsChain.nil⟩
      ⟨[i], List.IsChain.singleton i⟩)
    (hS : ∀ c v w, S c (A v w) = A (prefixFlip c v) (prefixFlip c w))
    {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue S y p = A (tailVertex p) (headVertex p) := by
  induction n generalizing i with
  | zero => exact hy i
  | succ n ih =>
    rw [pathValue_succ, ih p.2, hS, tailVertex_succ, headVertex_succ]

end ColoredPathAverage

end Problem367

end OAI
