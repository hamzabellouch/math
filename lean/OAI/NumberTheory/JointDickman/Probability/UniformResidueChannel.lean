import OAI.NumberTheory.JointDickman.Probability.ChannelGrid

namespace OAI

/-! # Uniform residue attenuation on the actual refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def manuscriptChannel (m₁ B q : ℕ)
    (f : (auxiliaryPrimes B → Bool) → ℝ) :
    Fin (channelFineCount m₁ B) × (ZMod q)ˣ → ℝ :=
  finiteChannel (fullPrimeMass (auxiliaryPrimes B))
    (fun _ => channelMesh (channelFineCount m₁ B) / (q.totient : ℝ))
    (partialFairPrimeTransition (auxiliaryPrimes B)
      (logResidueCell B q (channelLower (channelFineCount m₁ B))
        (channelUpper (channelFineCount m₁ B)))) f

open Classical in
/-- Residue dependence tends to zero uniformly on the unit ball, including
inputs varying with B and the modulus. All arithmetic hypotheses are the
precise previously published inputs. -/
theorem manuscriptChannel_residue_envelope
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C T : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < T ∧
      ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          (manuscriptChannel m₁ B q f a -
            finiteResidueAverage (fun r => manuscriptChannel m₁ B q f (a.1, r))) ^ 2) ≤
        residueDecayEnvelope M C T B * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, T, hM0, hC, hT, hbound⟩ := primeResidueChannel_from_published hSD hSW hM hMP
  refine ⟨M, C, T, hM0, hC, hT, ?_⟩
  intro m₁ hm₁
  filter_upwards [hbound, channelFineCount_eventually_le_square hm₁, eventually_ge_atTop 1]
    with B hboundB hnB hB
  intro q _ hq f
  have hBpos : 0 < B := by omega
  have hn := channelFineCount_pos hm₁ hBpos
  have hqB : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) := by
    have hreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
    calc
      (q : ℝ) ≤ B := by exact_mod_cast hq
      _ = (B : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hreal (by norm_num)
  have hδ := channelMesh_pos hn
  have hmain := hboundB (Fin (channelFineCount m₁ B)) q hqB
    (channelLower (channelFineCount m₁ B)) (channelUpper (channelFineCount m₁ B))
    (channelCells_disjoint hn) (channelLower_ge _)
    (fun i => by linarith [channel_width _ i])
    (fun i => (channelUpper_le hn i).trans (by norm_num))
    (channelMesh (channelFineCount m₁ B)) hδ (channel_width _) f
  have hmass := channel_total_mass (q := q) hn
  have herr := residueChannelError_le_envelope (M := M) hC.le hT.le hBpos
    (channel_atom_lower hBpos hn hnB hq)
    (show 0 ≤ ∑ _a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
      channelMesh (channelFineCount m₁ B) / (q.totient : ℝ) by rw [hmass]; norm_num)
    (show (∑ _a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
      channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) ≤ 3 by rw [hmass]; norm_num)
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  exact hmain.trans (mul_le_mul_of_nonneg_right herr hin)

open Classical in
theorem manuscriptChannel_residue_attenuation
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          (manuscriptChannel m₁ B q f a -
            finiteResidueAverage (fun r => manuscriptChannel m₁ B q f (a.1, r))) ^ 2) ≤
        ε B * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, T, _, _, _, hbound⟩ := manuscriptChannel_residue_envelope hSD hSW hM hMP
  exact ⟨residueDecayEnvelope M C T, residueDecayEnvelope_tendsto M C T, hbound⟩

end JointDickman

end OAI
