import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingTrial
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.CircleParameterData

theorem prod_block_eq_fin {A : Type*} [CommMonoid A]
    (p : CircleParameterData) (j : ℕ) (hj : 1 ≤ j) (f : ℕ → A) :
    (∏ i ∈ p.block j, f i) =
      ∏ i : Fin (p.m j), f (p.blockEnd (j - 1) + i.val + 1) := by
  classical
  have hend : p.blockEnd j = p.blockEnd (j - 1) + p.m j := by
    simpa only [Nat.sub_add_cancel hj] using p.blockEnd_succ (j - 1)
  symm
  apply Finset.prod_bij (fun i _ => p.blockEnd (j - 1) + i.val + 1)
  · intro i hi
    rw [mem_block_iff, hend]
    have h := i.isLt
    omega
  · intro i hi k hk heq
    apply Fin.ext
    omega
  · intro i hi
    obtain ⟨hlo, hhi⟩ := (p.mem_block_iff j i).mp hi
    rw [hend] at hhi
    refine ⟨⟨i - p.blockEnd (j - 1) - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i hi
    rfl

theorem samplingAverage_eq_characterAverage (p : CircleParameterData)
    (θ : ℝ) (j r : ℕ) (hj : 1 ≤ j) (endpoint : Bool) (x : Circle) :
    p.samplingAverage θ j r endpoint x =
      CharacterSampling.average (p.m j) (p.samples j r) endpoint
        (fun i : Fin (p.m j) => p.alpha θ (p.blockEnd (j - 1) + i.val + 1))
        (fun i : Fin (p.m j) =>
          (p.q (p.blockEnd (j - 1) + i.val + 1) : ℤ) • x) := by
  unfold samplingAverage CharacterSampling.average
  rw [one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [prod_block_eq_fin p j hj]
  apply Finset.prod_congr rfl
  intro i hi
  rw [CharacterSampling.kernel_eq_parameter_orientedKernel]
  rfl

end Invariant233.CircleParameterData

end

end OAI
