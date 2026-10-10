import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma alternating_vector_transversal {n : ℕ} {C : Type*} (lam : Partition n)
    (color : Fin n → C) (v : Specht lam) (hv : v ≠ 0)
    (hswap : ∀ i j, i ≠ j → color i = color j →
      spechtRepresentation lam (Equiv.swap i j) v = -v) :
    ∃ g : SymmetricGroup n, ∀ x y,
      lam.rowOf x = lam.rowOf y → color (g x) = color (g y) → x = y := by
  have hev : ∃ g, spechtInclusion lam v g ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply Subtype.ext
    exact PiLp.ext (fun g => h g)
  obtain ⟨g, hg⟩ := hev
  refine ⟨g, ?_⟩
  intro x y hr hc
  by_contra hxy
  have he := congrArg (fun z : Specht lam => spechtInclusion lam z g)
    (hswap (g x) (g y) (g.injective.ne hxy) hc)
  have hs : Equiv.swap (g x) (g y) * g = g * Equiv.swap x y := by
    apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  change spechtInclusion lam v ((Equiv.swap (g x) (g y))⁻¹ * g) =
    -(spechtInclusion lam v g) at he
  rw [Equiv.swap_inv, hs, specht_right_row lam v
    ⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩ g] at he
  apply hg
  linear_combination he / 2

def topRowCount (lam : YoungDiagram) (k : ℕ) : ℕ :=
  (lam.cells.filter (fun c => c.1 < k)).card

lemma topRowCount_eq_filter {n : ℕ} (lam : Partition n) (k : ℕ) :
    topRowCount lam.1 k = (Finset.univ.filter (fun x : Fin n => lam.rowOf x < k)).card := by
  rw [topRowCount]
  apply Finset.card_bij (fun c hc => lam.tableau ⟨c, (Finset.mem_filter.mp hc).1⟩)
  · intro c hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Partition.rowOf, Equiv.symm_apply_apply] using (Finset.mem_filter.mp hc).2
  · intro c hc e he hce
    exact congrArg Subtype.val (lam.tableau.injective hce)
  · intro x hx
    refine ⟨(lam.tableau.symm x).1,
      Finset.mem_filter.mpr ⟨(lam.tableau.symm x).2, (Finset.mem_filter.mp hx).2⟩, ?_⟩
    exact lam.tableau.apply_symm_apply x

lemma topRowCount_eq_sum_columns (lam : YoungDiagram) (k : ℕ) :
    topRowCount lam k = ∑ j : Fin (lam.rowLen 0), min k (lam.colLen j) := by
  let μ : Partition lam.card := ⟨lam, rfl⟩
  rw [topRowCount_eq_filter μ]
  change (Finset.univ.filter (fun x : Fin lam.card => μ.rowOf x < k)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← μ.colEquiv.sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  have hr (i : Fin (lam.colLen j)) : μ.rowOf (μ.colEquiv ⟨j,i⟩) = i.val := by
    simp [Partition.rowOf, Partition.colEquiv, μ]
  simp only [hr, ← Finset.card_eq_sum_ones, ← Finset.sum_filter]
  have he : (Finset.univ.filter (fun i : Fin (lam.colLen j) => i.val < k)).card =
      min k (lam.colLen j) := by
    let e : {i : Fin (lam.colLen j) // i.val < k} ≃ Fin (min k (lam.colLen j)) := {
      toFun i := ⟨i.val.val, lt_min i.2 i.val.isLt⟩
      invFun i := ⟨⟨i.val, i.isLt.trans_le (min_le_right _ _)⟩,
        i.isLt.trans_le (min_le_left _ _)⟩
      left_inv i := rfl
      right_inv i := rfl }
    rw [← Fintype.card_subtype]
    simpa using Fintype.card_congr e
  exact he

lemma topRowCount_eq_sum_rows (lam : YoungDiagram) (k : ℕ) :
    topRowCount lam k = ∑ i ∈ Finset.range k, lam.rowLen i := by
  unfold topRowCount
  let S := lam.cells.filter (fun c => c.1 < k)
  have he (i : ℕ) (hi : i ∈ Finset.range k) :
      (S.filter (fun c => c.1 = i)).card = lam.rowLen i := by
    rw [← Finset.card_range (lam.rowLen i)]
    apply Finset.card_nbij (fun c : ℕ × ℕ => c.2) (t := Finset.range (lam.rowLen i))
    · intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hc, he⟩
      have h := YoungDiagram.mem_iff_lt_rowLen.mp (Finset.mem_filter.mp hc).1
      apply Finset.mem_range.mpr
      simpa only [he] using h
    · intro c hc e he hce
      have hc' := (Finset.mem_filter.mp hc).2
      have he' := (Finset.mem_filter.mp he).2
      exact Prod.ext (hc'.trans he'.symm) hce
    · intro j hj
      refine ⟨(i,j), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj), Finset.mem_range.mp hi⟩, rfl⟩
  change S.card = _
  calc
    _ = ∑ i ∈ Finset.range k, (S.filter (fun c => c.1 = i)).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
        |>.trans (by simp only [S, Finset.mem_range, Finset.filter_filter, and_self])
    _ = _ := Finset.sum_congr rfl he

lemma transversal_topRowCount_le {n : ℕ} {C : Type*} [Fintype C]
    (lam : Partition n) (color : Fin n → C) (g : SymmetricGroup n)
    (hg : ∀ x y, lam.rowOf x = lam.rowOf y → color (g x) = color (g y) → x = y)
    (k : ℕ) :
    topRowCount lam.1 k ≤ ∑ c, min k (Fintype.card {x : Fin n // color x = c}) := by
  let S := Finset.univ.filter (fun x : Fin n => lam.rowOf x < k)
  rw [topRowCount_eq_filter]
  calc
    S.card = ∑ c, (S.filter (fun x => color (g x) = c)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _) 
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply le_min
      · calc
          _ ≤ (Finset.range k).card := by
            apply Finset.card_le_card_of_injOn lam.rowOf
            · intro x hx
              exact Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
            · intro x hx y hy hxy
              exact hg x y hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
          _ = k := Finset.card_range _
      · rw [Fintype.card_subtype]
        apply Finset.card_le_card_of_injOn g
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · exact g.injective.injOn

end SignedSweeps
end

end OAI
