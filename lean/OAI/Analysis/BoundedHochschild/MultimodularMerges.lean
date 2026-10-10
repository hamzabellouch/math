import OAI.Analysis.BoundedHochschild.MultimodularInsertion

namespace OAI

/-! Multiplying adjacent inputs is compatible with module balance. These
identities supply the interior faces of the relative Hochschild complex. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_left_module {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x 0 (r * x 0)) k =
      Function.update (mergeInputs x k) 0 (r * mergeInputs x k 0) := by
  ext i
  by_cases hi : i = 0
  · subst i
    by_cases hk : k = 0
    · subst k
      simp [mergeInputs, mul_assoc]
    · have hkpos : (0 : Fin (n + 1)) < k := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hk)
      simp [mergeInputs, hkpos]
  · have his : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h
      exact hi (Fin.ext (congrArg (fun j : Fin (n + 2) => j.val) h))
    simp only [mergeInputs, Function.update_of_ne hi, Function.update_of_ne his,
      Function.update_of_ne (Fin.succ_ne_zero i)]

lemma mergeInputs_right_module {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x (Fin.last (n + 1)) (x (Fin.last (n + 1)) * r)) k =
      Function.update (mergeInputs x k) (Fin.last n) (mergeInputs x k (Fin.last n) * r) := by
  ext i
  by_cases hi : i = Fin.last n
  · subst i
    by_cases hk : k = Fin.last n
    · subst k
      simp [mergeInputs, mul_assoc]
    · have hklt : k < Fin.last n := lt_of_le_of_ne (Fin.le_last _) hk
      simp [mergeInputs, not_lt_of_ge (Fin.le_last k), Ne.symm hk]
  · have his : i.succ ≠ Fin.last (n + 1) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    simp only [mergeInputs, Function.update_of_ne hi,
      Function.update_of_ne (ne_of_lt (Fin.castSucc_lt_last i)), Function.update_of_ne his]

lemma mergeInputs_balance_at {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x k.castSucc (x k.castSucc * r)) k =
      mergeInputs (Function.update x k.succ (r * x k.succ)) k := by
  ext i
  by_cases hik : i = k
  · subst i
    simp [mergeInputs, ne_of_lt (Fin.castSucc_lt_succ (i := k)),
      ne_of_gt (Fin.castSucc_lt_succ (i := k)), mul_assoc]
  · by_cases hlt : i < k
    · have hic : i.castSucc ≠ k.castSucc := by simpa using hik
      have his : i.castSucc ≠ k.succ := ne_of_lt (lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hlt)
        Fin.castSucc_lt_succ)
      simp only [mergeInputs, ite_eq_left hlt, Function.update_of_ne hic, Function.update_of_ne his]
    · have his : i.succ ≠ k.succ := by simpa using hik
      have hic : i.succ ≠ k.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_castSucc] at hv
        have hv' : k.val ≤ i.val := le_of_not_gt hlt
        omega
      simp only [mergeInputs, ite_eq_right hlt, ite_eq_right hik, Function.update_of_ne his, Function.update_of_ne hic]

end BoundedHochschild.KadisonRingrose

end

end OAI
