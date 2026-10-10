import OAI.Analysis.BoundedHochschild.NormalMultimodularity

namespace OAI

/-! Inserting the identity in a multimodular cochain retains its module
identities, including the balance across the deleted input. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma multimodularAt_curryMid_one {n : ℕ} (f : Cochain M (n + 2)) (r : M)
    (hf : MultimodularAt f r) (k : Fin (n + 2)) :
    MultimodularAt (f.curryMid k 1) r := by
  constructor
  · intro x
    change f (k.insertNth 1 (Function.update x 0 (r * x 0))) = r * f (k.insertNth (α := fun _ => M) 1 x)
    rw [Fin.insertNth_update]
    by_cases hk : k = 0
    · subst k
      have h := hf.balance ((0 : Fin (n + 2)).insertNth 1 x) (0 : Fin (n + 1))
      have hl := hf.left ((0 : Fin (n + 2)).insertNth 1 x)
      simp only [Fin.succAbove_zero, Fin.insertNth_zero', Fin.cons_zero,
        Fin.castSucc_zero, one_mul, mul_one] at h hl ⊢
      exact h.symm.trans hl
    · have hs : k.succAbove (0 : Fin (n + 1)) = 0 := Fin.succAbove_ne_zero_zero hk
      have hv : k.insertNth (α := fun _ => M) 1 x 0 = x 0 := by
        rw [← hs]
        exact Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x 0
      simpa only [hs, hv] using hf.left (k.insertNth (α := fun _ => M) 1 x)
  · intro x
    change f (k.insertNth 1 (Function.update x (Fin.last n) (x (Fin.last n) * r))) =
      f (k.insertNth (α := fun _ => M) 1 x) * r
    rw [Fin.insertNth_update]
    by_cases hk : k = Fin.last (n + 1)
    · subst k
      have h := hf.balance ((Fin.last (n + 1)).insertNth 1 x) (Fin.last n)
      have hr := hf.right ((Fin.last (n + 1)).insertNth 1 x)
      simp only [Fin.succAbove_last, Fin.insertNth_last', Fin.snoc_last,
        Fin.snoc_castSucc, Fin.succ_last, one_mul, mul_one] at h hr ⊢
      exact h.trans hr
    · have hs := Fin.succAbove_ne_last_last hk
      have hv : k.insertNth (α := fun _ => M) 1 x (Fin.last (n + 1)) = x (Fin.last n) := by
        rw [← hs]
        exact Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x (Fin.last n)
      simpa only [hs, hv] using hf.right (k.insertNth (α := fun _ => M) 1 x)
  · intro x j
    change f (k.insertNth 1 (Function.update x j.castSucc (x j.castSucc * r))) =
      f (k.insertNth 1 (Function.update x j.succ (r * x j.succ)))
    rw [Fin.insertNth_update, Fin.insertNth_update]
    let y := k.insertNth (α := fun _ => M) 1 x
    have hv (i : Fin (n + 1)) : y (k.succAbove i) = x i :=
      Fin.insertNth_apply_succAbove (α := fun _ => M) k 1 x i
    by_cases hk : k.val ≤ j.val
    · have hs₀ : k.succAbove j.castSucc = j.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hk)
      have hs₁ : k.succAbove j.succ = j.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
      have h₀ : y j.succ.castSucc = x j.castSucc := by
        simpa only [hs₀, Fin.castSucc_succ] using hv j.castSucc
      have h₁ : y j.succ.succ = x j.succ := by simpa only [hs₁] using hv j.succ
      simpa only [hs₀, hs₁, ← Fin.castSucc_succ, h₀, h₁] using hf.balance y j.succ
    · by_cases hk' : k.val = j.val + 1
      · have he : k = j.castSucc.succ := Fin.ext hk'
        have hs₀ : k.succAbove j.castSucc = j.castSucc.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
        have hs₁ : k.succAbove j.succ = j.succ.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
        have h₀ : y j.castSucc.castSucc = x j.castSucc := by simpa only [hs₀] using hv j.castSucc
        have h₁ : y j.succ.succ = x j.succ := by simpa only [hs₁] using hv j.succ
        have hmid : y j.castSucc.succ = 1 := by rw [← he]; exact Fin.insertNth_apply_same (α := fun _ => M) k 1 x
        have ha := hf.balance y j.castSucc
        have hb := hf.balance y j.succ
        simp only [h₀, hmid, mul_one] at ha
        simp only [Fin.castSucc_succ, hmid, h₁, one_mul] at hb
        simpa only [hs₀, hs₁] using ha.trans hb
      · have hs₀ : k.succAbove j.castSucc = j.castSucc.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
        have hs₁ : k.succAbove j.succ = j.succ.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
        have h₀ : y j.castSucc.castSucc = x j.castSucc := by simpa only [hs₀] using hv j.castSucc
        have h₁ : y j.castSucc.succ = x j.succ := by simpa only [hs₁, Fin.castSucc_succ] using hv j.succ
        simpa only [hs₀, hs₁, Fin.castSucc_succ, h₀, h₁] using hf.balance y j.castSucc

end BoundedHochschild.KadisonRingrose

end

end OAI
