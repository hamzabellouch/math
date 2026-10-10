import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

structure RootedTemplate (k : ℕ) where
  edges : Graph k
  roots : Finset (Fin k)
  simple : ∀ e ∈ edges, e.card = 2
  independent : ∀ e ∈ edges, ¬ e ⊆ roots

abbrev RootedInjection {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :=
  {φ : Fin k ↪ Fin n // ∀ v : {v // v ∈ T.roots}, φ v = ψ v}

def imageEdges {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n) : Graph n :=
  T.edges.image (fun e => e.map φ)

@[simp] theorem imageEdges_card {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n) :
    (imageEdges T φ).card = T.edges.card := by
  apply Finset.card_image_of_injective
  intro e f h
  exact Finset.map_injective φ h

theorem imageEdges_simple {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n)
    {e : Finset (Fin n)} (he : e ∈ imageEdges T φ) : e.card = 2 := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  simpa using T.simple f hf

noncomputable def rootedCount {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) : ℝ :=
  copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) G

noncomputable def rootedScaling {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card

theorem rootedCount_drift {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) (D δ : ℝ)
    (hdeg : ∀ e ∈ G, |(triangleDegree G e : ℝ) - D| ≤ δ)
    (hG : (triangles G).Nonempty) :
    |pmfMean (step G) (rootedCount T ψ) - rootedCount T ψ G +
      ((T.edges.card : ℝ) * D / (triangles G).card) * rootedCount T ψ G| ≤
      (((T.edges.card : ℝ) * δ + (T.edges.card : ℝ) ^ 2) / (triangles G).card) *
        rootedCount T ψ G := by
  exact copyCount_drift_error (fun φ : RootedInjection T ψ => imageEdges T φ.val)
    G T.edges.card D δ (fun φ => imageEdges_card T φ.val) hdeg hG

end SharpTerminalLeave

end
end

end OAI
