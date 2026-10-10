import OAI.MeasureTheory.Falconer.Estimates.ScalarPorousLevels

namespace OAI

/-! Ordered endpoints selected from the actual porous levels, extended
 monotonically beyond the final endpoint without altering selected data. -/
namespace Falconer.Regularization

 theorem scalar_porous_endpoint_enumeration (M : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range M) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ e 0 = 0 ∧ e S.card ≤ M ∧
      (∀ j, 0 < j → j ≤ S.card → e j-1 ∈ S) ∧ (∀ i ∈ S, i < e S.card) := by
  classical
  let E := S.orderIsoOfFin rfl
  let g : ℕ → ℕ := fun i => if hi : i < S.card then (E ⟨i,hi⟩).val else M+(i-S.card)
  have hgmem : ∀ i < S.card, g i ∈ S := by
    intro i hi
    simpa only [g,dite_eq_left hi] using (E ⟨i,hi⟩).property
  have hgbound : ∀ i < S.card, g i < M := fun i hi => Finset.mem_range.mp (hS (hgmem i hi))
  have hg : StrictMono g := by
    intro i j hij
    by_cases hi : i < S.card
    · by_cases hj : j < S.card
      · have hh : (E ⟨i,hi⟩).val < (E ⟨j,hj⟩).val :=
          E.strictMono (show (⟨i,hi⟩ : Fin S.card) < ⟨j,hj⟩ from hij)
        simpa only [g,dite_eq_left hi,dite_eq_left hj] using hh
      · have hh := hgbound i hi
        simp only [g,dite_eq_left hi,dite_eq_right hj]
        change (E ⟨i,hi⟩).val < M+(j-S.card)
        have hh' : (E ⟨i,hi⟩).val < M := by simpa only [g,dite_eq_left hi] using hh
        omega
    · have hj : ¬j < S.card := by omega
      simp only [g,dite_eq_right hi,dite_eq_right hj]
      omega
  let e : ℕ → ℕ := fun j => if j = 0 then 0 else g (j-1)+1
  have he : StrictMono e := by
    intro i j hij
    by_cases hi : i = 0
    · simp only [e,ite_eq_left hi,ite_eq_right (show j ≠ 0 by omega)]
      omega
    · have hj : j ≠ 0 := by omega
      simp only [e,ite_eq_right hi,ite_eq_right hj]
      exact Nat.add_lt_add_right (hg (by omega : i-1 < j-1)) 1
  have hemem : ∀ j, 0 < j → j ≤ S.card → e j-1 ∈ S := by
    intro j hj hjS
    simp only [e,ite_eq_right (show j ≠ 0 by omega),Nat.add_sub_cancel]
    exact hgmem (j-1) (by omega)
  refine ⟨e,he,by simp [e],?_,hemem,?_⟩
  · by_cases hz : S.card = 0
    · simp [hz,e]
    · have hp := hgbound (S.card-1) (by omega)
      simp only [e,ite_eq_right hz]
      omega
  · intro i hi
    let j := (E.symm ⟨i,hi⟩).val
    have hj : j < S.card := (E.symm ⟨i,hi⟩).isLt
    have hgj : g j = i := by
      simp only [g,dite_eq_left hj,j]
      exact congrArg Subtype.val (E.apply_symm_apply ⟨i,hi⟩)
    have hle : g j ≤ g (S.card-1) := hg.monotone (by omega)
    have hz : S.card ≠ 0 := by omega
    simp only [e,ite_eq_right hz]
    omega

end Falconer.Regularization

end OAI
