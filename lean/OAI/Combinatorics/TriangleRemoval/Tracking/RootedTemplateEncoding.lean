import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RootedTemplates

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def rootedTemplateEncoding {k : ℕ} (T : RootedTemplate k) :
    Graph k × Finset (Fin k) := (T.edges,T.roots)

lemma rootedTemplateEncoding_injective (k : ℕ) :
    Function.Injective (rootedTemplateEncoding (k := k)) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

noncomputable instance rootedTemplateFintype (k : ℕ) : Fintype (RootedTemplate k) :=
  Fintype.ofInjective rootedTemplateEncoding (rootedTemplateEncoding_injective k)

abbrev RootedCountIndex (H n : ℕ) :=
  Σ k : Fin (H+1), Σ T : RootedTemplate k.val, ({v // v ∈ T.roots} ↪ Fin n)

noncomputable def rootedFamilySize (H : ℕ) : ℕ :=
  ∑ k : Fin (H+1), Fintype.card (RootedTemplate k.val)

lemma rootInjection_card_le {k n : ℕ} (T : RootedTemplate k) :
    Fintype.card ({v // v ∈ T.roots} ↪ Fin n) ≤ n^T.roots.card := by
  have hh := Fintype.card_le_of_injective
    (fun f : {v // v ∈ T.roots} ↪ Fin n => (f : {v // v ∈ T.roots} → Fin n))
    (fun _ _ h => DFunLike.coe_injective h)
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using hh

theorem rootedCountIndex_card_le (H n : ℕ) :
    Fintype.card (RootedCountIndex H n) ≤ rootedFamilySize H * (n+1)^H := by
  classical
  unfold RootedCountIndex
  simp only [Fintype.card_sigma]
  calc
    _ ≤ ∑ k : Fin (H+1), ∑ T : RootedTemplate k.val, (n+1)^H := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro T _
      apply (rootInjection_card_le T).trans
      have hr : T.roots.card ≤ k.val := by
        simpa using (Finset.card_le_univ T.roots)
      calc
        n^T.roots.card ≤ (n+1)^T.roots.card := Nat.pow_le_pow_left (Nat.le_succ n) _
        _ ≤ (n+1)^H := Nat.pow_le_pow_right (by omega) (by omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      rfl

def rootedIndexRequired {H n : ℕ} (i : RootedCountIndex H n) :
    RootedInjection i.2.1 i.2.2 → Graph n := fun φ => imageEdges i.2.1 φ.val

@[simp] lemma rootedIndex_copyCount {H n : ℕ} (i : RootedCountIndex H n) (G : Graph n) :
    copyCount (rootedIndexRequired i) G = rootedCount i.2.1 i.2.2 G := rfl

end SharpTerminalLeave

end

end OAI
