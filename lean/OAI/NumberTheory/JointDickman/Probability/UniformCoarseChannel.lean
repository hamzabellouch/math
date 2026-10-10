import OAI.NumberTheory.JointDickman.Amplification.CoarseErrorLimit

namespace OAI

/-! # The manuscript's coarse channel on its refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

noncomputable def groupedManuscriptChannel (m B : ℕ)
    (f : (auxiliaryPrimes B → Bool) → ℝ) :
    Fin m × Fin (channelBlockCount m B) → ℝ :=
  finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => channelMesh (channelFineCount m B))
    (partialFairPrimeTransition (auxiliaryPrimes B)
      (logarithmicCell B (groupedLower m (channelBlockCount m B))
        (groupedUpper m (channelBlockCount m B)))) f

open Classical in
theorem groupedManuscriptChannel_coarse_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A C T : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < T ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 → ∃ M L : ℝ≥0,
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B) *
        (groupedManuscriptChannel m B f a -
          finiteResidueAverage (fun r => groupedManuscriptChannel m B f (a.1, r))) ^ 2) ≤
        coarseChannelError A C T M L θ B (channelMesh (channelFineCount m B)) (channelMesh m) (5 / 2) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨A, C, T, hA, hC, hT, hbound⟩ := primeLogCoarse_from_published hSD hSW hM hMP
  refine ⟨A, C, T, hA, hC, hT, ?_⟩
  intro θ hθ hθmax
  obtain ⟨M, L, hbound⟩ := hbound θ hθ hθmax
  refine ⟨M, L, ?_⟩
  intro m hm
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro f
  let k := channelBlockCount m B
  have hk : 0 < k := by
    have hn := channelFineCount_pos hm hB
    change 0 < m * k at hn
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0] at hn
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hh := hboundB (Fin m) (Fin k) (groupedLower m k) (groupedUpper m k)
    (groupedCells_disjoint hm hk) (groupedLower_ge m k)
    (fun a => (groupedUpper_le hm hk a).trans (by norm_num))
    (channelMesh (m * k)) (channelMesh m) (channelMesh_pos (Nat.mul_pos hm hk))
    (channelMesh_pos hm).le (grouped_width m k) (groupedLower_diameter hm hk) f
  rw [grouped_total_mass hm hk] at hh
  exact hh

end JointDickman

end OAI
