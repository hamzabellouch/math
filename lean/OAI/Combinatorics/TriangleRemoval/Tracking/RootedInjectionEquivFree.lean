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

noncomputable def rootedInjectionEquivFree {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    RootedInjection T ψ ≃
      ({v : Fin k // v ∉ T.roots} ↪ {w : Fin n // w ∉ Set.range ψ}) := by
  classical
  refine {
    toFun := fun φ => {
      toFun := fun v => ⟨φ.val v,?_⟩
      inj' := ?_ }
    invFun := fun f => ⟨{
      toFun := fun v => if hv : v ∈ T.roots then ψ ⟨v,hv⟩ else f ⟨v,hv⟩
      inj' := ?_ },?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro h
    obtain ⟨a,ha⟩ := h
    rw [← φ.property a] at ha
    have hh : a.val = v.val := φ.val.injective ha
    exact v.property (hh ▸ a.property)
  · intro a b hab
    apply Subtype.ext
    exact φ.val.injective (congrArg Subtype.val hab)
  · intro a b hab
    dsimp at hab
    split_ifs at hab with ha hb hb
    · exact congrArg Subtype.val (ψ.injective hab)
    · exact ((f ⟨b,hb⟩).property ⟨⟨a,ha⟩,hab⟩).elim
    · exact ((f ⟨a,ha⟩).property ⟨⟨b,hb⟩,hab.symm⟩).elim
    · exact congrArg Subtype.val (f.injective (Subtype.ext hab))
  · intro v
    change (if hv : v.val ∈ T.roots then ψ ⟨v.val,hv⟩ else _) = ψ v
    simp only [dite_eq_left v.property]
  · intro φ
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    change (if hv : v ∈ T.roots then ψ ⟨v,hv⟩ else φ.val v) = φ.val v
    split_ifs with hv
    · exact (φ.property ⟨v,hv⟩).symm
    · rfl
  · intro f
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change (if hv : v.val ∈ T.roots then ψ ⟨v.val,hv⟩ else (f ⟨v.val,hv⟩).val) = (f v).val
    simp only [dite_eq_right v.property]

theorem card_rootedInjection {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    Fintype.card (RootedInjection T ψ) =
      (n-T.roots.card).descFactorial (k-T.roots.card) := by
  classical
  rw [Fintype.card_congr (rootedInjectionEquivFree T ψ),Fintype.card_embedding_eq]
  have hfree : Fintype.card {v : Fin k // v ∉ T.roots} = k-T.roots.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      (Fintype.card_subtype_compl (fun v : Fin k => v ∈ T.roots))
  have htarget : Fintype.card {w : Fin n // w ∉ Set.range ψ} = n-T.roots.card := by
    calc
      _ = Fintype.card (↑((Set.range ψ)ᶜ)) := Fintype.card_congr (Equiv.refl _)
      _ = n-T.roots.card := by
        rw [Fintype.card_compl_set,Fintype.card_range,Fintype.card_fin,Fintype.card_coe]
  rw [hfree,htarget]

theorem rootedCount_completeGraph {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    rootedCount T ψ (completeGraph n) =
      ((n-T.roots.card).descFactorial (k-T.roots.card) : ℝ) := by
  classical
  unfold rootedCount copyCount
  have hcontains : ∀ φ : RootedInjection T ψ, imageEdges T φ.val ⊆ completeGraph n := by
    intro φ e he
    exact mem_completeGraph.mpr (imageEdges_simple T φ.val he)
  simp only [intact,ite_eq_left (hcontains _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,card_rootedInjection]

end SharpTerminalLeave

end

end OAI
