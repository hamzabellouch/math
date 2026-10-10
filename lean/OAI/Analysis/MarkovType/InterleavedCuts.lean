import OAI.Analysis.MarkovType.EndNorm

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def interleavedCuts {M : ℕ} (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ)
    (B : ℕ) (i : Fin (2 * M + 2 + 1)) : ℕ :=
  if h0 : i.val = 0 then 0
  else if hlast : i.val = 2 * M + 2 then B
  else if hodd : i.val % 2 = 1 then
    r ⟨i.val / 2, by have := i.isLt; omega⟩
  else
    t ⟨i.val / 2 - 1, by have := i.isLt; omega⟩

@[simp] theorem interleavedCuts_zero {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ) :
    interleavedCuts r t B 0 = 0 := by
  simp [interleavedCuts]

@[simp] theorem interleavedCuts_last {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ) :
    interleavedCuts r t B (Fin.last (2 * M + 2)) = B := by
  simp [interleavedCuts]

theorem interleavedCuts_odd {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B j : ℕ) (hj : j ≤ M) :
    interleavedCuts r t B ⟨2 * j + 1, by omega⟩ =
      r ⟨j, by omega⟩ := by
  unfold interleavedCuts
  dsimp only
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  apply congrArg r
  apply Fin.ext
  dsimp only
  omega

theorem interleavedCuts_even {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B j : ℕ) (hj : j < M) :
    interleavedCuts r t B ⟨2 * j + 2, by omega⟩ =
      t ⟨j, hj⟩ := by
  unfold interleavedCuts
  dsimp only
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
  apply congrArg t
  apply Fin.ext
  dsimp only
  omega

theorem interleavedCuts_strictMono {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ)
    (hr0 : 0 < r 0)
    (hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ)
    (hrB : r (Fin.last M) < B) :
    StrictMono (interleavedCuts r t B) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  have hk := k.isLt
  by_cases hk0 : k.val = 0
  · have hleft : k.castSucc = 0 := Fin.ext hk0
    have hright : k.succ = ⟨2 * 0 + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hleft, hright, interleavedCuts_zero,
      interleavedCuts_odd r t B 0 (Nat.zero_le M)]
    exact hr0
  by_cases hklast : k.val = 2 * M + 1
  · have hleft : k.castSucc = ⟨2 * M + 1, by omega⟩ := Fin.ext hklast
    have hright : k.succ = Fin.last (2 * M + 2) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [hleft, hright, interleavedCuts_last,
      interleavedCuts_odd r t B M (le_refl M)]
    exact hrB
  by_cases hodd : k.val % 2 = 1
  · let j := k.val / 2
    have hj : j < M := by dsimp [j]; omega
    have hleft : k.castSucc = ⟨2 * j + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp [j]
      omega
    have hright : k.succ = ⟨2 * j + 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [j]
      omega
    rw [hleft, hright, interleavedCuts_odd r t B j (Nat.le_of_lt hj),
      interleavedCuts_even r t B j hj]
    exact (hrt ⟨j, hj⟩).1
  · let j := k.val / 2 - 1
    have hj : j < M := by dsimp [j]; omega
    have hleft : k.castSucc = ⟨2 * j + 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp [j]
      omega
    have hright : k.succ = ⟨2 * (j + 1) + 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [j]
      omega
    rw [hleft, hright, interleavedCuts_even r t B j hj,
      interleavedCuts_odd r t B (j + 1) (by omega)]
    exact (hrt ⟨j, hj⟩).2

namespace OrderedNorm

theorem alternatingNorm_six_le_of_interleaved (N : OrderedNorm) (M B : ℕ)
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ)
    (hr0 : 0 < r 0)
    (hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ)
    (hrB : r (Fin.last M) < B)
    (G : C00) (hG : C00.SupportedBelow G B) (htotal : prefixCut G B = 0)
    (ell U V : ℝ) (hell : 0 ≤ ell) (hgap : U - V = ell)
    (hr : ∀ i, prefixCut G (r i) = V)
    (ht : ∀ i, prefixCut G (t i) = U) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  apply N.alternatingNorm_six_le_of_levels M ell U V hell hgap
    (interleavedCuts r t B)
    (interleavedCuts_strictMono r t B hr0 hrt hrB).monotone
    (interleavedCuts_zero r t B) G
  · simpa only [interleavedCuts_last] using hG
  · simpa only [interleavedCuts_last] using htotal
  · intro j hj
    rw [interleavedCuts_odd r t B j hj]
    exact hr ⟨j, by omega⟩
  · intro j hj
    rw [interleavedCuts_even r t B j hj]
    exact ht ⟨j, hj⟩

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
