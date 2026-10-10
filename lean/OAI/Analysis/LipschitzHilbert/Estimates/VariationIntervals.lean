import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation

namespace OAI

/-! Disjoint interval selections, including selections depending on a point,
are controlled by one finite cubic variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private def intervalPoint {S : ℕ} (a b : Fin S → ℕ) (N j : ℕ) : ℕ :=
  if h : j / 2 < S then if j % 2 = 0 then a ⟨j / 2, h⟩ else b ⟨j / 2, h⟩ else N

private theorem intervalPoint_le {S : ℕ} (a b : Fin S → ℕ) (N j : ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N) : intervalPoint a b N j ≤ N := by
  unfold intervalPoint
  split_ifs with h hpar
  · exact (hab _).trans (hb _)
  · exact hb _
  · exact le_rfl

private theorem intervalPoint_mono {S : ℕ} (a b : Fin S → ℕ) (N : ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) : Monotone (intervalPoint a b N) := by
  intro i j hij
  by_cases hj : j / 2 < S
  · have hi : i / 2 < S := by omega
    have hdiv : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
    by_cases heq : i / 2 = j / 2
    · have hidx : (⟨i / 2, hi⟩ : Fin S) = ⟨j / 2, hj⟩ := Fin.ext heq
      unfold intervalPoint
      rw [dite_eq_left hi, dite_eq_left hj, hidx]
      by_cases hip : i % 2 = 0
      · rw [ite_eq_left hip]
        by_cases hjp : j % 2 = 0
        · rw [ite_eq_left hjp]
        · rw [ite_eq_right hjp]
          exact hab _
      · rw [ite_eq_right hip]
        by_cases hjp : j % 2 = 0
        · omega
        · rw [ite_eq_right hjp]
    · have hlt : (⟨i / 2, hi⟩ : Fin S) < ⟨j / 2, hj⟩ := by
        change i / 2 < j / 2
        omega
      have hsep := horder ⟨i / 2, hi⟩ ⟨j / 2, hj⟩ hlt
      unfold intervalPoint
      rw [dite_eq_left hi, dite_eq_left hj]
      split_ifs
      · exact (hab _).trans hsep
      · exact ((hab _).trans hsep).trans (hab _)
      · exact hsep
      · exact hsep.trans (hab _)
  · have hj' : intervalPoint a b N j = N := by simp only [intervalPoint, dite_eq_right hj]
    rw [hj']
    exact intervalPoint_le a b N i hab hb

/-- Padding with the terminal endpoint embeds all selected intervals into
a monotone partition of the stopped sequence. There is no measurability
assumption on how the intervals were selected. -/
theorem ordered_intervals_le_variation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N S : ℕ) (a b : Fin S → ℕ) (hS : S ≤ N)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    (∑ i, ‖F (b i) - F (a i)‖ ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  classical
  let p : Fin (2 * N + 1) → Fin (2 * N + 1) := fun i =>
    ⟨intervalPoint a b N i, lt_of_le_of_lt (intervalPoint_le a b N i hab hb) (by omega)⟩
  have hp : Monotone p := fun i j hij => intervalPoint_mono a b N hab hb horder hij
  let e : Fin S → Fin (2 * N) := fun i => ⟨2 * i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp only [e] at h
    omega
  have hpa (i : Fin S) : (p (e i).castSucc).val = a i := by
    simp [p, e, intervalPoint, show (2 * i.val) / 2 = i.val by omega,
      show (2 * i.val) % 2 = 0 by omega, i.isLt]
  have hpb (i : Fin S) : (p (e i).succ).val = b i := by
    simp [p, e, intervalPoint, show (2 * i.val + 1) / 2 = i.val by omega, i.isLt]
  have hselect : (∑ i, ‖F (b i) - F (a i)‖ ^ 3) ≤
      ∑ i : Fin (2 * N), ‖F (min (p i.succ) N) - F (min (p i.castSucc) N)‖ ^ 3 := by
    refine Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
      e (fun i _ j _ hij => he hij) (Finset.subset_univ _) ?_ ?_
    · intro i _
      rw [hpa, hpb, min_eq_left (hb i), min_eq_left ((hab i).trans (hb i))]
    · intro i _ _
      positivity
  exact hselect.trans (partition_le_finiteCubicVariation
    (fun n => F (min n N)) (2 * N) p hp)

end LipschitzHilbert

end

end OAI
