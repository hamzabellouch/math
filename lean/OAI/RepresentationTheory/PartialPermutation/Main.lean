import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DeficitPlancherel
import OAI.RepresentationTheory.PartialPermutation.NormBounds

namespace OAI

namespace PartialPermutation
noncomputable section
open scoped Classical

theorem complementaryCosets_finite : ComplementaryCosetsFiniteStatement := by
  intro X _ _ b hb M hnonempty hdis _ V _ _ _ ρ hirr hρ f B u hf hm hu hcap
  let := hirr
  have hB : 0 ≤ B := by
    let i : Fin b := ⟨0,hb⟩
    have hp : (0:ℝ) < (blockSubgroup (M i)).index := by
      exact_mod_cast Nat.pos_of_ne_zero (blockSubgroup (M i)).index_ne_zero_of_finite
    have hz : 0 ≤ B / (blockSubgroup (M i)).index :=
      (Finset.sum_nonneg (fun (g : blockSubgroup (M i)) _ => hf (1*g))).trans (hcap i 1)
    simpa only [div_mul_cancel₀ B hp.ne'] using mul_nonneg hz hp.le
  have hsum : (∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u) ≤
      (b:ℝ)*symmetricDegreeConstant u := by
    calc
      _ ≤ ∑ _i : Fin b, symmetricDegreeConstant u := by
        apply Finset.sum_le_sum
        intro i _
        let : Nonempty (M i) := (hnonempty i).to_subtype
        exact symmetricInverseDegreeSum_le_constant (by exact Fintype.card_pos) hu
      _ = _ := by simp
  have hs : 0 ≤ ∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u := by
    exact Finset.sum_nonneg (fun _ _ => inverseDegreeSum_nonneg _ _)
  have hR : 0 ≤ (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b:ℝ)) := Real.rpow_nonneg (by positivity) _
  have hcoef : B * mass f * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) ≤
      B * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) := by
    calc
      _ ≤ B * 1 * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) hR
      _ = _ := by ring
  have hHS : hsNormSq (complexFourier ρ (fun g => f g)) ≤
      b * B * symmetricDegreeConstant u * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) := by
    calc
      _ ≤ _ := by
        have h := inverse_degree_sum_transfer ρ (fun i => blockSubgroup (M i)) hb hρ
          (fun i j hij g hg k hk => blockSubgroup_commute (hdis hij) hg hk) f B u hf hu hcap
        rw [inverseDegreeSum_block_sum M u] at h
        exact h
      _ ≤ (B * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ))) *
          ((b:ℝ)*symmetricDegreeConstant u) :=
        mul_le_mul hcoef hsum hs (mul_nonneg hB hR)
      _ = _ := by ring
  exact ⟨hHS,(opNorm_sq_le_hsNormSq _).trans hHS⟩

end
end PartialPermutation

end OAI
