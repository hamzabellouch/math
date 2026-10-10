import OAI.Analysis.Laughlin.Exterior.Scaling

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def pairEnd (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, c i j • (annihilate j * annihilate i)

noncomputable def sourcePairEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairEnd Q (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ))

noncomputable def limitPairEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairEnd Q (fun i j => ((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ))

noncomputable def physicalScaling (Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (modeFactor Q i.val : ℂ))

noncomputable def physicalScalingInv (Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (modeFactor Q i.val : ℂ)⁻¹)

theorem pairEnd_smul (Q : ℕ) (r : ℂ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q (fun i j => r*c i j) = r • pairEnd Q c := by
  simp only [pairEnd, Finset.smul_sum, smul_smul]

theorem pairEnd_scaling (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (d : Fin (Q+1) → ℂ) (x : Space Q) :
    pairEnd Q c (exteriorScaling Q d x) =
      exteriorScaling Q d (pairEnd Q (fun i j => c i j*d i*d j) x) := by
  simp only [pairEnd, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    map_sum, map_smul, annihilate_scaling, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

theorem sourcePair_intertwining (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) (x : Space Q) :
    physicalScaling Q (sourcePairEnd Q p x) =
      (pairFactor Q p : ℂ) • limitPairEnd Q p (physicalScaling Q x) := by
  have hc : (fun i j : Fin (Q+1) => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) =
      (fun i j => (pairFactor Q p : ℂ)*
        (((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ)*
          (modeFactor Q i.val : ℂ)*(modeFactor Q j.val : ℂ))) := by
    funext i j
    rw [pairCoefficient_conjugation Q p hQ hp]
    push_cast
    ring
  unfold sourcePairEnd limitPairEnd physicalScaling
  rw [hc, pairEnd_smul, LinearMap.smul_apply, map_smul, pairEnd_scaling]

theorem physicalScaling_left_inverse (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    physicalScalingInv Q (physicalScaling Q x) = x := by
  apply exteriorScaling_inverse
  intro i
  exact_mod_cast (ne_of_gt (modeFactor_pos Q hQ i))

theorem sourcePair_conjugation (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) (x : Space Q) :
    sourcePairEnd Q p x = (pairFactor Q p : ℂ) •
      physicalScalingInv Q (limitPairEnd Q p (physicalScaling Q x)) := by
  have h := congrArg (physicalScalingInv Q) (sourcePair_intertwining Q p hQ hp x)
  rw [physicalScaling_left_inverse Q hQ, map_smul] at h
  exact h

end Laughlin.Fock

end OAI
