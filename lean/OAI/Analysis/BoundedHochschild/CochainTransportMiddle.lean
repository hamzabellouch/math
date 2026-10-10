import OAI.Analysis.BoundedHochschild.CochainTransportFaces

namespace OAI

/-! Interior Hochschild faces delete the unitary at the multiplied
boundary. Its two adjacent factors cancel exactly. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTuple_merge {n : ℕ} (u : Fin (n + 3) → unitary M)
    (x : Fin (n + 2) → M) (k : Fin (n + 1)) :
    mergeInputs (cochainUnitaryTuple u x) k =
      cochainUnitaryTuple (k.castSucc.succ.removeNth u) (mergeInputs x k) := by
  let p : Fin (n + 3) := k.castSucc.succ
  have hbefore (j : Fin (n + 2)) (hj : j.val < p.val) : p.removeNth u j = u j.castSucc := by
    rw [Fin.removeNth, Fin.succAbove_of_castSucc_lt _ _ hj]
  have hafter (j : Fin (n + 2)) (hj : p.val ≤ j.val) : p.removeNth u j = u j.succ := by
    rw [Fin.removeNth, Fin.succAbove_of_le_castSucc _ _ hj]
  change mergeInputs (cochainUnitaryTuple u x) k = cochainUnitaryTuple (p.removeNth u) (mergeInputs x k)
  ext i
  by_cases hik : i < k
  · have hi : i.val < k.val := hik
    simp only [mergeInputs, ite_eq_left hik, cochainUnitaryTuple]
    rw [hbefore i.castSucc (by dsimp [p]; omega),
      hbefore i.succ (by dsimp [p]; omega)]
    rfl
  · by_cases hie : i = k
    · subst i
      simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true, cochainUnitaryTuple]
      rw [hbefore k.castSucc (by dsimp [p]; simp), hafter k.succ (by dsimp [p]; simp)]
      simp only [Fin.castSucc_succ, mul_assoc]
      rw [← mul_assoc (star (u k.castSucc.succ : M)) (u k.castSucc.succ : M),
        Unitary.star_mul_self_of_mem (u k.castSucc.succ).property, one_mul]
    · have hi : k.val < i.val := by
        have hne : i.val ≠ k.val := fun h => hie (Fin.ext h)
        omega
      simp only [mergeInputs, ite_eq_right hik, ite_eq_right hie, cochainUnitaryTuple]
      rw [hafter i.castSucc (by dsimp [p]; omega),
        hafter i.succ (by dsimp [p]; omega)]
      rfl

lemma cochainUnitaryTransport_middleCoboundary {n : ℕ}
    (u : Fin (n + 3) → unitary M) (f : Cochain M (n + 1)) (k : Fin (n + 1)) :
    cochainUnitaryTransport u (middleCoboundary f k) =
      middleCoboundary (cochainUnitaryTransport (k.castSucc.succ.removeNth u) f) k := by
  ext x
  simp only [cochainUnitaryTransport_apply, middleCoboundary_apply, cochainUnitaryTuple_merge]
  have hzero : k.castSucc.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
  have hlast : k.castSucc.succ ≠ Fin.last (n + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp only [Fin.removeNth, Fin.succAbove_ne_zero_zero hzero,
    Fin.succAbove_ne_last_last hlast]

end BoundedHochschild.KadisonRingrose

end

end OAI
