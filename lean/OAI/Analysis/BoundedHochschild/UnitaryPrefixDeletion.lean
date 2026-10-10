import OAI.Analysis.BoundedHochschild.MultimodularTransport

namespace OAI

/-! Deleting a vertex from a prefix transport changes its cutoff exactly
when that vertex was already transported. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma unitaryPrefix_removeNth_before {n : ℕ} (u : Fin (n + 2) → unitary M)
    (p : Fin (n + 2)) (k : ℕ) (hpk : p.val < k) :
    p.removeNth (unitaryPrefix u k) = unitaryPrefix (p.removeNth u) (k - 1) := by
  funext j
  change (if (p.succAbove j).val < k then u (p.succAbove j) else 1) =
    (if j.val < k - 1 then u (p.succAbove j) else 1)
  by_cases hjp : j.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p j hjp]
    have hj : j.val < p.val := hjp
    simp only [Fin.val_castSucc, show j.val < k by omega,
      show j.val < k - 1 by omega, ite_true]
  · rw [Fin.succAbove_of_le_castSucc p j (le_of_not_gt hjp)]
    have hpj : p.val ≤ j.val := le_of_not_gt hjp
    have he : j.val + 1 < k ↔ j.val < k - 1 := by omega
    simp only [Fin.val_succ, he]

lemma unitaryPrefix_removeNth_after {n : ℕ} (u : Fin (n + 2) → unitary M)
    (p : Fin (n + 2)) (k : ℕ) (hkp : k ≤ p.val) :
    p.removeNth (unitaryPrefix u k) = unitaryPrefix (p.removeNth u) k := by
  funext j
  change (if (p.succAbove j).val < k then u (p.succAbove j) else 1) =
    (if j.val < k then u (p.succAbove j) else 1)
  by_cases hjp : j.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p j hjp]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p j (le_of_not_gt hjp)]
    have hpj : p.val ≤ j.val := le_of_not_gt hjp
    simp only [Fin.val_succ, show ¬j.val + 1 < k by omega,
      show ¬j.val < k by omega, ite_false]

lemma unitaryPrefix_tail {n : ℕ} (u : Fin (n + 2) → unitary M) (k : ℕ) :
    Fin.tail (unitaryPrefix u (k + 1)) = unitaryPrefix (Fin.tail u) k := by
  simpa only [Fin.removeNth_zero, Nat.add_sub_cancel] using
    unitaryPrefix_removeNth_before u 0 (k + 1) (by simp)

lemma unitaryPrefix_init {n : ℕ} (u : Fin (n + 2) → unitary M) (k : ℕ) :
    Fin.init (unitaryPrefix u k) = unitaryPrefix (Fin.init u) k := by
  funext j
  rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
