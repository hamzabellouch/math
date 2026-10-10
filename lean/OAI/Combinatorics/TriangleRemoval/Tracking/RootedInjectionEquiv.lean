import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RootedTemplates

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def rootedInjectionEquiv {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    RootedInjection T ψ ≃
      ({v : Fin k // v ∉ T.roots} ↪ {w : Fin n // w ∉ Set.range ψ}) := by
  classical
  let restrict (f : RootedInjection T ψ) :
      {v : Fin k // v ∉ T.roots} ↪ {w : Fin n // w ∉ Set.range ψ} :=
    ⟨fun v => ⟨f.val v.val, by
        rintro ⟨r,hr⟩
        have he : f.val r.val = f.val v.val := (f.property r).trans hr
        exact v.property (f.val.injective he ▸ r.property)⟩,
      fun a b h => Subtype.ext (f.val.injective (congrArg Subtype.val h))⟩
  let extend (g : {v : Fin k // v ∉ T.roots} ↪
      {w : Fin n // w ∉ Set.range ψ}) : RootedInjection T ψ :=
    ⟨⟨fun v => if h : v ∈ T.roots then ψ ⟨v,h⟩ else g ⟨v,h⟩,
      by
        intro a b hab
        by_cases ha : a ∈ T.roots <;> by_cases hb : b ∈ T.roots
        · simp only [ha,hb,↓reduceDIte] at hab
          exact congrArg Subtype.val (ψ.injective hab)
        · simp only [ha,hb,↓reduceDIte] at hab
          exact False.elim ((g ⟨b,hb⟩).property ⟨⟨a,ha⟩,hab⟩)
        · simp only [ha,hb,↓reduceDIte] at hab
          exact False.elim ((g ⟨a,ha⟩).property ⟨⟨b,hb⟩,hab.symm⟩)
        · simp only [ha,hb,↓reduceDIte] at hab
          exact congrArg Subtype.val (g.injective (Subtype.ext hab))⟩,
      by
        intro v
        change (if h : v.val ∈ T.roots then ψ ⟨v.val,h⟩ else (g ⟨v.val,h⟩).val) = ψ v
        exact dite_eq_left v.property⟩
  refine ⟨restrict,extend,?_,?_⟩
  · intro f
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    change (if h : v ∈ T.roots then ψ ⟨v,h⟩ else (restrict f ⟨v,h⟩).val) = f.val v
    split_ifs with h
    · exact (f.property ⟨v,h⟩).symm
    · rfl
  · intro g
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    change (if h : v.val ∈ T.roots then ψ ⟨v.val,h⟩ else (g ⟨v.val,h⟩).val) = _
    simp only [v.property,↓reduceDIte]

theorem rootedInjection_card {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    Fintype.card (RootedInjection T ψ) =
      (n - T.roots.card).descFactorial (k - T.roots.card) := by
  classical
  rw [Fintype.card_congr (rootedInjectionEquiv T ψ), Fintype.card_embedding_eq]
  have hd : Fintype.card {v : Fin k // v ∉ T.roots} = k - T.roots.card := by
    simp
  have hc : Fintype.card {w : Fin n // w ∉ Set.range ψ} = n - T.roots.card := by
    calc
      _ = Fintype.card ↑(Set.range ψ)ᶜ := Fintype.card_congr (Equiv.refl _)
      _ = _ := by simp only [Fintype.card_compl_set, Fintype.card_fin,
        Fintype.card_range, Fintype.card_coe]
  rw [hd,hc]

theorem rootedCount_complete {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    rootedCount T ψ (completeGraph n) =
      ((n - T.roots.card).descFactorial (k - T.roots.card) : ℝ) := by
  classical
  have hh (φ : RootedInjection T ψ) : imageEdges T φ.val ⊆ completeGraph n := by
    intro e he
    exact mem_completeGraph.mpr (imageEdges_simple T φ.val he)
  simp only [rootedCount, copyCount, intact, hh, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, rootedInjection_card]

end SharpTerminalLeave

end
end

end OAI
