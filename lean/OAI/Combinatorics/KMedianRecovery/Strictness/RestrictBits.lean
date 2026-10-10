import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Average

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling

def restrictBits {b p : ℕ} (h : b ≤ p) (bits : Fin p → Bool) : Fin b → Bool :=
  fun i => bits ⟨i.val,i.isLt.trans_le h⟩

def splitBits {b p : ℕ} (h : b ≤ p) :
    (Fin p → Bool) ≃ (Fin b → Bool) × (Fin (p-b) → Bool) :=
  (((finSumFinEquiv (m := b) (n := p-b)).trans
    (finCongr (Nat.add_sub_of_le h))).symm.arrowCongr (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin b) (Fin (p-b)) Bool)

lemma splitBits_fst {b p : ℕ} (h : b ≤ p) (bits : Fin p → Bool) :
    (splitBits h bits).1 = restrictBits h bits := by
  funext i
  rfl

lemma average_restrictBits {b p : ℕ} (h : b ≤ p) (X : (Fin b → Bool) → ℝ) :
    average (fun bits => X (restrictBits h bits)) = average X := by
  rw [average_equiv (splitBits h) _ (fun q => X q.1) (fun bits => by rw [splitBits_fst]),average_prod]
  simp only [average_const]

lemma probability_restrictBits {b p : ℕ} (h : b ≤ p) (P : (Fin b → Bool) → Prop) :
    probability (fun bits => P (restrictBits h bits)) = probability P := by
  classical
  exact average_restrictBits h (fun bits => if P bits then 1 else 0)

end MetricKMedianRecovery.FiniteSampling

end OAI
