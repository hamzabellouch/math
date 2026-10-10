import Mathlib.Data.Fin.Basic
import OAI.Analysis.Laughlin.Operators.LocalFourIndexEquiv

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

def localFourCountEquiv (D : ℕ) :
    LocalFourIndex D ≃ (n : Fin (D+1)) × Fin ((n.val+1)/2) where
  toFun b := ⟨⟨b.val.2.1.val+b.val.2.2.val,by have := b.property.1; omega⟩,
    ⟨b.val.2.1.val,by dsimp; have := b.property.2; omega⟩⟩
  invFun b := ⟨(⟨D-b.1.val,by omega⟩,⟨b.2.val,by have := b.2.isLt; omega⟩,
    ⟨b.1.val-b.2.val,by omega⟩),by
      have := b.2.isLt
      constructor
      · dsimp; omega
      · change b.2.val < b.1.val-b.2.val
        omega⟩
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; dsimp; have := b.property.1; omega
    · apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp; omega
  right_inv b := by
    rcases b with ⟨n,j⟩
    have hj : j.val ≤ n.val := by have := j.isLt; omega
    dsimp
    have hn : j.val+(n.val-j.val)=n.val := by omega
    apply Sigma.ext
    · exact Fin.ext hn
    · apply (Fin.heq_ext_iff (by dsimp; rw [hn])).mpr
      rfl

theorem localFourIndex_card_sum (D : ℕ) :
    Fintype.card (LocalFourIndex D) = ∑ n : Fin (D+1), (n.val+1)/2 := by
  rw [Fintype.card_congr (localFourCountEquiv D),Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem localFourIndex_card_retained (D : ℕ) (hD : D ≤ 23) :
    Fintype.card (LocalFourIndex D) = (D+1)^2/4 := by
  rw [localFourIndex_card_sum]
  interval_cases D <;> norm_num [Fin.sum_univ_succ]

end Laughlin.Spin

end OAI
