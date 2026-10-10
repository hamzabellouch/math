import OAI.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget

namespace OAI

section

namespace Erdos3

theorem exists_residue_good_scalar_kernel_bound (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    ∃ s : I ↪ J, ∀ (M : ℕ), 0 < M → ∀ η : ℝ, 0 < η → ∃ B L₀ : ℕ,
      0 < B ∧ ∃ hsize : (Fintype.card I + 1) * M ≤ L₀,
      ∀ (L : ℕ) (hL : 0 < L) (hlarge : L₀ ≤ L)
        (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
        (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M),
        (FiniteProbabilityWeights.pi (fun j =>
          scalarCubeResidueWeights I L M hL (m j) (r j) (hm j) (hmM j)
            (hsize.trans hlarge))).eventProbability
              (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) ≤ η := by
  obtain ⟨s, hs⟩ := exists_uniform_good_scalar_kernel_bound I J hJ
  refine ⟨s, fun M hM η hη => ?_⟩
  let C := (scalarCubeResidueDensityCap I M) ^ Fintype.card J
  have hC : 0 < C := pow_pos (scalarCubeResidueDensityCap_pos I M hM) _
  obtain ⟨B, L₁, hB, hL₁, hprob⟩ := hs (η / C) (div_pos hη hC)
  refine ⟨B, max L₁ ((Fintype.card I + 1) * M), hB, Nat.le_max_right _ _, ?_⟩
  intro L hL hlarge m r hm hmM
  have hsize : (Fintype.card I + 1) * M ≤ L := (Nat.le_max_right _ _).trans hlarge
  calc
    _ ≤ C * (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) :=
      scalarCubeResidue_pi_eventProbability_le I J L M hL m r hm hmM hsize _
    _ ≤ C * (η / C) := mul_le_mul_of_nonneg_left
      (hprob L hL ((Nat.le_max_left _ _).trans hlarge)) hC.le
    _ = η := by field_simp

end Erdos3

end

end OAI
