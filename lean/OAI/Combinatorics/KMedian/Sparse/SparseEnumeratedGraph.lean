import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGraphLaw

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

def lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) : I → Finset I :=
  fun i => (G (enum.symm i)).map enum.toEmbedding

omit [DecidableEq I] in
@[simp] theorem mem_lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) (h i : I) :
    h∈lift enum G i ↔ enum.symm h∈G (enum.symm i) := by
  simp only [lift,mem_map,Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a,ha,he⟩
    simpa only [← he,Equiv.symm_apply_apply] using ha
  · intro ha
    exact ⟨enum.symm h,ha,enum.apply_symm_apply h⟩

def law (enum : Fin n ≃ I) (q : I → I → ℚ) : SparseIntegerLaw (I → Finset I) :=
  (SparseGraph.law (fun h i => q (enum h) (enum i))).map (lift enum)

omit [DecidableEq I] in
theorem length_unconditional (enum : Fin n ≃ I) (q : I → I → ℚ) :
    (law enum q).length ≤ n*n+(n*n)*(n*n)+1 :=
  SparseGraph.run_length _ _

omit [DecidableEq I] in
theorem length (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) :
    (law enum q).length ≤ n*n+(n*n)*(n*n)+1 :=
  (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).1

omit [DecidableEq I] in
theorem columns_card (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ))
    (a : Fin (law enum q).length) (i : I) :
    ((law enum q).states[a.val] i).card=Δ := by
  have he := SparseIntegerLaw.map_states (SparseGraph.law (fun h i => q (enum h) (enum i))) (lift enum) a
  change (law enum q).states[a.val]=_ at he
  rw [he]
  rw [lift,card_map]
  exact (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.1 a _

theorem single (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) (h i : I) :
    (law enum q).moment (fun G => if h∈G i then 1 else 0)=q h i := by
  rw [law,SparseIntegerLaw.map_moment]
  simp only [mem_lift]
  have hh := (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.2.1 (enum.symm h) (enum.symm i)
  simpa only [SparseGraph.edge,Equiv.apply_symm_apply] using hh

theorem pair (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) (h l i j : I) (hij : i≠j) :
    (law enum q).moment (fun G => (if h∈G i then 1 else 0)*(if l∈G j then 1 else 0))=q h i*q l j := by
  rw [law,SparseIntegerLaw.map_moment]
  simp only [mem_lift]
  have hh := (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.2.2 (enum.symm h) (enum.symm l)
      (enum.symm i) (enum.symm j) (fun he => hij (enum.symm.injective he))
  simpa only [SparseGraph.edge,Equiv.apply_symm_apply] using hh

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
