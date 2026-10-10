import OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual

namespace OAI


noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem energy_le_exp_of_normalized_log_le {a m L : ℝ} (hm : 0 < m)
    (h : Real.log a / m ^ 2 - Real.log 2 / 2 ≤ L) :
    a ≤ Real.exp (m ^ 2 * (L + Real.log 2 / 2)) := by
  have hlog : Real.log a / m ^ 2 ≤ L + Real.log 2 / 2 := by linarith only [h]
  have hscaled : Real.log a ≤ m ^ 2 * (L + Real.log 2 / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hm)).mp hlog
  exact (Real.le_exp_log a).trans (Real.exp_le_exp.mpr hscaled)

theorem realEnergyMajorantOne_uniform_exp {lam Bx Bs : ℝ} (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤
        Real.exp ((n N : ℝ) ^ 2 *
          (realEnergyDualConstant 1 p v Bx Bs + d + Real.log 2 / 2)) := by
  obtain ⟨M, hM⟩ := realEnergyMajorantOne_uniform_dual hlam p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  apply energy_le_exp_of_normalized_log_le hn
  exact hM N (by omega) x s hx hs hx0 hxi hsi hcase

theorem realEnergyMajorantTwo_uniform_exp {Bx Bs : ℝ}
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      realEnergyMajorantTwo N x s ≤
        Real.exp ((n N : ℝ) ^ 2 *
          (realEnergyDualConstant 2 p v Bx Bs + d + Real.log 2 / 2)) := by
  obtain ⟨M, hM⟩ := realEnergyMajorantTwo_uniform_dual p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  apply energy_le_exp_of_normalized_log_le hn
  exact hM N (by omega) x s hx hs hx0 hxi hsi

end InternalCatalan

end

end OAI
