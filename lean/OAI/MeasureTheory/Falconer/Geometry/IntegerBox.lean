import OAI.MeasureTheory.Falconer.Incidence.PublishedLoomisWhitney

namespace OAI

/-! # Product grid boxes for the general-dimensional tube count -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

theorem integer_box_card (T : Finset (Fin n → ℤ)) (x : Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ)) (hT : ∀ z ∈ T, ∀ j, |(z j:ℝ)-x j| ≤ r) :
    T.card ≤ (2*L+1)^n := by
  classical
  let B (j : Fin n) := Finset.Icc (round (x j)-(L:ℤ)) (round (x j)+(L:ℤ))
  have hsub : T ⊆ Fintype.piFinset B := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_Icc.mpr (integer_near_real_bounds (z j) (x j) r L (hT z hz j) hL)
  have hB (j : Fin n) : (B j).card = 2*L+1 := by
    dsimp [B]
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by simp only [Fintype.card_piFinset,hB,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin])

theorem integer_box_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (Fin n → ℤ)) (A : Finset ι) (x : ι → Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, ∀ j, |(z j:ℝ)-x a j| ≤ r) :
    T.card ≤ A.card*(2*L+1)^n := by
  classical
  let F : ι → Finset (Fin n → ℤ) := fun a => T.filter (fun z => ∀ j, |(z j:ℝ)-x a j| ≤ r)
  have hs : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hs
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^n := Finset.sum_le_sum (fun a _ =>
      integer_box_card (F a) (x a) r L hL (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = _ := by simp

end Falconer

end OAI
