import OAI.Analysis.Laughlin.Exterior.PairConjugation

namespace OAI

namespace Laughlin.Fock

noncomputable def sourceFourEnd (Q p : ℕ) (j k : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  annihilate k * annihilate j * sourcePairEnd Q p

noncomputable def limitFourEnd (Q p : ℕ) (j k : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  annihilate k * annihilate j * limitPairEnd Q p

theorem sourceFour_intertwining (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (j k : Fin (Q+1)) (x : Space Q) :
    ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) •
      physicalScaling Q (sourceFourEnd Q p j k x) =
        (pairFactor Q p : ℂ) • limitFourEnd Q p j k (physicalScaling Q x) := by
  have h := congrArg (fun y => annihilate k (annihilate j y))
    (sourcePair_intertwining Q p hQ hp x)
  simpa only [sourceFourEnd, limitFourEnd, Module.End.mul_apply, physicalScaling,
    annihilate_scaling, map_smul, smul_smul] using h

theorem sourceFour_conjugation (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (j k : Fin (Q+1)) (x : Space Q) :
    sourceFourEnd Q p j k x =
      ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
        physicalScalingInv Q (limitFourEnd Q p j k (physicalScaling Q x)) := by
  have h := congrArg (physicalScalingInv Q) (sourceFour_intertwining Q p hQ hp j k x)
  rw [map_smul, physicalScaling_left_inverse Q hQ, map_smul] at h
  have hj : (modeFactor Q j.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ j)
  have hk : (modeFactor Q k.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ k)
  have hd := mul_ne_zero hj hk
  calc
    _ = ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))⁻¹ •
        (((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) • sourceFourEnd Q p j k x) := by
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    _ = _ := by
      rw [h, smul_smul]
      congr 1
      ring

end Laughlin.Fock

end OAI
