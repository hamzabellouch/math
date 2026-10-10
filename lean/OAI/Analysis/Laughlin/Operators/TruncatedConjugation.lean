import OAI.Analysis.Laughlin.Asymptotics.TruncatedScaling

namespace OAI

namespace Laughlin.Fock

theorem truncated_sourcePair_intertwining (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    truncatedScaling L Q (sourcePairEnd Q p x) =
      (pairFactor Q p : ℂ) • limitPairEnd Q p (truncatedScaling L Q x) := by
  have hc : (fun i j : Fin (Q+1) => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) =
      (fun i j => (pairFactor Q p : ℂ)*
        (((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ)*
          (truncatedModeFactor L Q i : ℂ)*(truncatedModeFactor L Q j : ℂ))) := by
    funext i j
    rw [pairCoefficient_conjugation Q p hQ hp]
    by_cases hs : i.val+j.val=p+1
    · simp only [truncatedModeFactor,ite_eq_left (show i.val≤L by omega),ite_eq_left (show j.val≤L by omega)]
      push_cast
      ring
    · simp [pairLimitCoefficient,hs]
  unfold sourcePairEnd limitPairEnd truncatedScaling
  rw [hc,pairEnd_smul,LinearMap.smul_apply,map_smul,pairEnd_scaling]

theorem truncated_sourceFour_conjugation (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (j k : Fin (Q+1))
    (hjL : j.val ≤ L) (hkL : k.val ≤ L) (x : Space Q) :
    sourceFourEnd Q p j k x =
      ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
        truncatedScalingInv L Q (limitFourEnd Q p j k (truncatedScaling L Q x)) := by
  have h := congrArg (fun y => annihilate k (annihilate j y))
    (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  have he : ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) •
      truncatedScaling L Q (sourceFourEnd Q p j k x) =
        (pairFactor Q p : ℂ) • limitFourEnd Q p j k (truncatedScaling L Q x) := by
    simpa only [sourceFourEnd,limitFourEnd,Module.End.mul_apply,truncatedScaling,
      annihilate_scaling,map_smul,smul_smul,truncatedModeFactor,ite_eq_left hjL,ite_eq_left hkL] using h
  have h' := congrArg (truncatedScalingInv L Q) he
  rw [map_smul,truncatedScaling_left_inverse L Q hQ,map_smul] at h'
  have hj : (modeFactor Q j.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ j)
  have hk : (modeFactor Q k.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ k)
  have hd := mul_ne_zero hj hk
  calc
    _ = ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))⁻¹ •
        (((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) • sourceFourEnd Q p j k x) := by
      rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
    _ = _ := by rw [h',smul_smul]; congr 1; ring

end Laughlin.Fock

end OAI
