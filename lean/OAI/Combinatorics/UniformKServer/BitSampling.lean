import Mathlib

namespace OAI

namespace UniformKServer.BitSampling

def bitsEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2^b) :=
  (Equiv.piCongrRight (fun _ : Fin b => finTwoEquiv.symm)).trans
    (finPiFinEquiv.trans (finCongr (by simp)))

def row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b)
    (coins : Fin b → Bool) : Fin k :=
  (finSigmaFinEquiv.symm ((finCongr hN).symm (bitsEquiv b coins))).1

def cumulative {k : ℕ} (N : Fin k → ℕ) (j : Fin k) : ℕ :=
  ∑ i : Fin j.val, N (Fin.castLE j.isLt.le i)

theorem exact_row_proof {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  let e : (Fin b → Bool) ≃ ((j : Fin k) × Fin (N j)) :=
    (bitsEquiv b).trans ((finCongr hN).symm.trans finSigmaFinEquiv.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro coins
    exact Nat.zero_lt_of_lt (e coins).2.isLt
  · intro coins
    have he := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply
      ((finCongr hN).symm (bitsEquiv b coins)))
    rw [finSigmaFinEquiv_apply] at he
    change cumulative N (row N hN coins) + (e coins).2.val = (bitsEquiv b coins).val at he
    have ht := (e coins).2.isLt
    change (e coins).2.val < N (row N hN coins) at ht
    omega
  · intro f
    have hs : (∑ coins : Fin b → Bool, f (row N hN coins)) =
        ∑ j, (N j : ℝ) * f j := by
      calc
        _ = ∑ v : (j : Fin k) × Fin (N j), f v.1 :=
          e.sum_comp (fun v => f v.1)
        _ = _ := by simp [Fintype.sum_sigma]
    rw [hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring

                                                                            
theorem exact_row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  exact exact_row_proof N hN

end UniformKServer.BitSampling



end OAI
