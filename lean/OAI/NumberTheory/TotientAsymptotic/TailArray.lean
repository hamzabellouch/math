import OAI.NumberTheory.TotientAsymptotic.RemainderSplit

namespace OAI

/-! The discrete tail, in the coordinate order used by the full simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailVector {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℝ :=
  fun i => tailLog η (H-1-i.val)

lemma tailVector_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) : 0 ≤ tailVector η i := by
  apply tailLog_nonneg hη
  apply Finset.mem_Ico.mpr
  have := i.isLt
  omega

lemma D_eq_tailVector_sum {H : ℕ} (η : TailDatum H) (hPH : P H ≤ H) (h : ℕ) :
    D h η = ∑ i : Fin (H-P H), a (h-(H-1-i.val))*tailVector η i := by
  unfold D
  apply Finset.sum_bij (fun l hl => (⟨H-1-l, by
    have := Finset.mem_Ico.mp hl
    omega⟩ : Fin (H-P H)))
  · intro l hl
    exact Finset.mem_univ _
  · intro l hl k hk he
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · intro i _
    have hi := i.isLt
    refine ⟨H-1-i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp only
    omega
  · intro l hl
    have := Finset.mem_Ico.mp hl
    dsimp only [tailVector]
    have he : H-1-(H-1-l)=l := by omega
    rw [he]

lemma tailVector_row {H : ℕ} (η : TailDatum H) (i : Fin (H-P H)) :
    (∑ j : Fin (H-P H), if i < j then a (j.val-i.val)*tailVector η j else 0) =
      ∑ l ∈ Finset.Ico (P H) (H-1-i.val), a (H-1-i.val-l)*tailLog η l := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => H-1-j.val)
  · intro j hj
    have hj' : i < j := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hjb := j.isLt
    exact Finset.mem_Ico.mpr (by simp only [Fin.lt_def] at hj'; omega)
  · intro j hj k hk he
    apply Fin.ext
    have := j.isLt
    have := k.isLt
    omega
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    refine ⟨⟨H-1-l, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change i.val < H-1-l
      omega
    · simp only
      omega
  · intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hjb := j.isLt
    dsimp only [tailVector]
    congr 2
    simp only [Fin.lt_def] at hij
    omega

lemma tailVector_simplex {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) :
    (∑ j : Fin (H-P H), if i < j then a (j.val-i.val)*tailVector η j else 0) ≤
      (1+(1/10000 : ℝ)*Real.exp (-((H-1-i.val : ℕ) : ℝ)/40))*tailVector η i := by
  rw [tailVector_row]
  have hi : H-1-i.val ∈ Finset.Ico (P H) H := by
    have := i.isLt
    exact Finset.mem_Ico.mpr (by omega)
  exact (hη.2.2.1 _ hi).2.2.2

end TotientAsymptotic

end

end OAI
