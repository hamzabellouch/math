import OAI.NumberTheory.TwoPoint.Walks.RetainedComplexRows
import OAI.NumberTheory.TwoPoint.Bounds.ActualBilinearTesting

namespace OAI

/-! Ten actual compressed-graph tests control each directed complex block. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def ambientComplexBlockTest {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) : ℂ :=
  let c : ℤ := (t + 2 : ℕ)
  let vf := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) (fun n => star (F n))
  let vg := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) G
  inner ℂ vf (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
    L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c vg)

lemma retainedComplexBlock_ten_tests {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (D : ℤ) (hD : 0 < D)
    (hshift : ∀ d : (j : Fin J) → P j, ∀ q ∈ Q, eligible (∏ j, (d j).val) q →
      D ≤ (h * q * ∏ j, (d j).val : ℕ) ∧ (h * q * ∏ j, (d j).val : ℕ) < 2 * D)
    (F G : ℤ → ℂ) (t : ℕ) :
    retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t =
      ∑ c : ForwardColorCode, ambientComplexBlockTest P M Q Qp u eligible L K W extra h
        gate keep (fun n => if sourceColor D c n then F n else 0)
          (fun n => if targetColor D c n then G n else 0) t := by
  have hg : ∀ d (i j : Fin M),
      (gate d ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) ∧
        keep ((i.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((j.val : ℤ) + (t + 2 : ℕ))) ↔
      (gate d ((j.val : ℤ) + (t + 2 : ℕ)) ((i.val : ℤ) + (t + 2 : ℕ)) ∧
        keep ((j.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((i.val : ℤ) + (t + 2 : ℕ))) := by
    intro d i j
    rw [hgate]
    tauto
  have hi := projected_prime_directed_identity P hprime hdisjoint
    (fun i : Fin M => (i.val : ℤ) + (t + 2 : ℕ)) Q Qp u eligible L K W extra h
    (fun d i j => gate d ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) ∧
      keep ((i.val : ℤ) + (t + 2 : ℕ)) ∧ keep ((j.val : ℤ) + (t + 2 : ℕ))) hg D hD hshift F G
  exact hi

lemma uniformAverage_norm_sum_le {C Ω : Type*} [Fintype C] [Fintype Ω]
    (T : C → Ω → ℂ) (B : ℝ) (hT : ∀ c, uniformAverage (fun x => ‖T c x‖) ≤ B) :
    uniformAverage (fun x => ‖∑ c, T c x‖) ≤ Fintype.card C * B := by
  calc
    _ ≤ uniformAverage (fun x => ∑ c, ‖T c x‖) := by
      unfold uniformAverage
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun x _ => norm_sum_le _ _)
    _ = ∑ c, uniformAverage (fun x => ‖T c x‖) := by
      unfold uniformAverage
      rw [sum_comm, sum_div]
    _ ≤ ∑ _c : C, B := sum_le_sum (fun c _ => hT c)
    _ = _ := by simp

lemma retainedComplexBlock_average_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M N : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (D : ℤ) (hD : 0 < D)
    (hshift : ∀ d : (j : Fin J) → P j, ∀ q ∈ Q, eligible (∏ j, (d j).val) q →
      D ≤ (h * q * ∏ j, (d j).val : ℕ) ∧ (h * q * ∏ j, (d j).val : ℕ) < 2 * D)
    (F G : ℤ → ℂ) (B : ℝ)
    (htest : ∀ c : ForwardColorCode, uniformAverage (fun t : Fin N =>
      ‖ambientComplexBlockTest P M Q Qp u eligible L K W extra h gate keep
        (fun n => if sourceColor D c n then F n else 0)
        (fun n => if targetColor D c n then G n else 0) t.val‖) ≤ B) :
    uniformAverage (fun t : Fin N =>
      ‖retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t.val‖) ≤
        10 * B := by
  simp_rw [retainedComplexBlock_ten_tests P hprime hdisjoint M Q Qp u eligible L K W
    extra h gate hgate keep D hD hshift F G]
  have hb := uniformAverage_norm_sum_le _ B htest
  simpa [ForwardColorCode] using hb

end TwoPointCorrelations

end OAI
