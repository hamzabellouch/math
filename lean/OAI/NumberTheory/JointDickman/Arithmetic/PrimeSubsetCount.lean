import OAI.NumberTheory.JointDickman.Arithmetic.PrimeGeneratingMean
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleBounds
import Mathlib.Data.Finset.Sort

namespace OAI

/-! # Bounding admissible prime subsets by ordered tuples -/
namespace JointDickman
open Finset

theorem boundedPrimeSubsets_fixed_card_le (P : Finset ℕ) (N h : ℕ) :
    ((boundedPrimeSubsets P N).filter (fun D => D.card = h)).card ≤
      primeTupleCount P h (N : ℝ) := by
  classical
  let S := (boundedPrimeSubsets P N).filter (fun D => D.card = h)
  let T := (Fintype.piFinset (fun _ : Fin h => P)).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)
  let f : Finset ℕ → (Fin h → ℕ) := fun D =>
    if hD : D.card = h then D.orderEmbOfFin hD else fun _ => 0
  have hs (D : Finset ℕ) (hD : D ∈ S) : D ⊆ P ∧ (∏ p ∈ D, p) ≤ N ∧ D.card = h := by
    obtain ⟨hDP,hcard⟩ := mem_filter.mp hD
    obtain ⟨hDP,hprod⟩ := mem_filter.mp hDP
    exact ⟨mem_powerset.mp hDP,hprod,hcard⟩
  have hmap : Set.MapsTo f S T := by
    intro D hD
    obtain ⟨hDP,hprod,hcard⟩ := hs D hD
    simp only [f,dite_eq_left hcard]
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => hDP (D.orderEmbOfFin_mem hcard i)),?_⟩
    have he : (∏ i : Fin h, D.orderEmbOfFin hcard i) = ∏ p ∈ D, p := by
      simpa only [prod_map,RelEmbedding.coe_toEmbedding] using congrArg (fun E : Finset ℕ => ∏ p ∈ E, p)
        (D.map_orderEmbOfFin_univ hcard)
    have her : (∏ i : Fin h, (D.orderEmbOfFin hcard i : ℝ)) = ((∏ p ∈ D, p : ℕ) : ℝ) := by
      exact_mod_cast he
    rw [her]
    exact_mod_cast hprod
  have hinj : (S : Set (Finset ℕ)).InjOn f := by
    intro D hD E hE hDE
    have hd := (hs D hD).2.2
    have he := (hs E hE).2.2
    have hiD : univ.image (f D) = D := by
      simpa only [f,dite_eq_left hd] using D.image_orderEmbOfFin_univ hd
    have hiE : univ.image (f E) = E := by
      simpa only [f,dite_eq_left he] using E.image_orderEmbOfFin_univ he
    rw [← hiD,← hiE,hDE]
  exact card_le_card_of_injOn f hmap hinj

theorem boundedPrimeSubsets_card_le (P : Finset ℕ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    (boundedPrimeSubsets P N).card ≤ ∑ h ∈ range (J+1), primeTupleCount P h (N : ℝ) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Finset.card)
    (t := range (J+1)) (fun D hD => mem_range.mpr (by have := hcard D hD; omega))]
  exact sum_le_sum (fun h _ => boundedPrimeSubsets_fixed_card_le P N h)

end JointDickman

end OAI
