import OAI.NumberTheory.JointDickman.Probability.UniformResidueChannel

namespace OAI

/-! # Uniform norm bound for the actual fair-split channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem manuscriptChannel_square_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          manuscriptChannel m₁ B q f a ^ 2) ≤
        K * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, hM0, hC, hbound⟩ := primeSite_interval_upper hSD hSW hM hMP
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2)
  refine ⟨M + C + 1, by positivity, ?_⟩
  intro m₁ hm₁
  filter_upwards [hbound, channelFineCount_eventually_le_square hm₁, eventually_ge_atTop 1]
    with B hboundB hnB hB
  intro q _ hq f
  have hBpos : 0 < B := by omega
  have hn := channelFineCount_pos hm₁ hBpos
  let n := channelFineCount m₁ B
  let m := channelMesh n / (q.totient : ℝ)
  let cell := logResidueCell B q (channelLower n) (channelUpper n)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hm : 0 < m := div_pos (channelMesh_pos hn) hφ
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hqB : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) := by
    calc
      (q : ℝ) ≤ B := by exact_mod_cast hq
      _ = (B : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
  have hmin := channel_atom_lower hBpos hn hnB hq
  have hE : C * (B : ℝ) ^ (-(80 : ℝ)) ≤ C * m := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (-(80 : ℝ)) ≤ -3)).trans hmin
  have hmar (a : Fin n × (ZMod q)ˣ) :
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x *
        partialFairPrimeTransition (auxiliaryPrimes B) cell x a) ≤ (M + C + 1) * m := by
    rcases a with ⟨d, r⟩
    rw [partialFairPrimeTransition_marginal]
    have hw : (fun p : auxiliaryPrimes B => (1 / (p.val : ℝ)) / 2) =
        (fun p : auxiliaryPrimes B => (1 / 2 : ℝ) / p.val) := by funext p; ring
    rw [hw]
    change optionCellMass _ (fun x => logResidueCell B q (channelLower n) (channelUpper n)
      (retainedPrimeProduct (auxiliaryPrimes B) x)) (d, r) ≤ _
    rw [primeLogCell_eq _ B q _ _ (channelCells_disjoint hn)]
    have hb := hboundB (channelLower n d) (channelUpper n d)
      ((by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (channelLower_ge n d))
      (by linarith [channel_width n d, channelMesh_pos hn])
      ((channelUpper_le hn d).trans (by norm_num)) q hqB r
    rw [channel_width] at hb
    have heq : M * channelMesh n / (q.totient : ℝ) = M * m := by dsimp [m]; ring
    rw [heq] at hb
    nlinarith
  exact finiteChannel_square_bound (fullPrimeMass (auxiliaryPrimes B)) (fun _ => m)
    (partialFairPrimeTransition (auxiliaryPrimes B) cell)
    (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B)) (fun _ => hm)
    (partialFairPrimeTransition_nonneg _ cell) (by positivity) hmar
    (partialFairPrimeTransition_sum_le _ cell) f

end JointDickman

end OAI
