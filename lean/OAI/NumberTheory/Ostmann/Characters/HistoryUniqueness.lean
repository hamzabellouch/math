import Mathlib

namespace OAI

namespace Ostmann.Characters

def frequencyDeterminant (v w v' w' : ℤ) : ℤ := v*w' - v'*w

theorem reversal_determinant_dvd {v w v' w' P P' s HL HR : ℤ}
    (h : v*HR-w*HL=s*P) (h' : v'*HR-w'*HL=s*P')
    (hcop : IsCoprime s HR) : s ∣ frequencyDeterminant v w v' w' := by
  apply hcop.dvd_of_dvd_mul_right
  refine ⟨P*w'-P'*w, ?_⟩
  unfold frequencyDeterminant
  nlinarith [congrArg (fun z : ℤ => z*w') h, congrArg (fun z : ℤ => z*w) h']

theorem reversal_determinant_zero {v w v' w' P P' s HL HR : ℤ}
    (h : v*HR-w*HL=s*P) (h' : v'*HR-w'*HL=s*P')
    (hcop : IsCoprime s HR)
    (hsmall : |frequencyDeterminant v w v' w'| < |s|) :
    frequencyDeterminant v w v' w' = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (reversal_determinant_dvd h h' hcop)
  have hn : ((frequencyDeterminant v w v' w').natAbs : ℤ) < (s.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using hsmall
  exact_mod_cast hn

theorem positive_coprime_denominator_unique {P P' w w' : ℤ}
    (hP : 0 < P) (hP' : 0 < P')
    (hc : IsCoprime P w) (hc' : IsCoprime P' w')
    (heq : P*w' = P'*w) : P = P' := by
  have hdiv : P ∣ P' := hc.dvd_of_dvd_mul_right ⟨w', heq.symm⟩
  have hdiv' : P' ∣ P := hc'.dvd_of_dvd_mul_right ⟨w, heq⟩
  have hn : P.natAbs = P'.natAbs := Nat.dvd_antisymm
    (Int.natAbs_dvd_natAbs.mpr hdiv) (Int.natAbs_dvd_natAbs.mpr hdiv')
  have hz := congrArg (fun n : ℕ => (n:ℤ)) hn
  simpa only [Int.natCast_natAbs, abs_of_pos hP, abs_of_pos hP'] using hz

theorem reversal_unique {v w v' w' P P' s HL HR : ℤ}
    (h : v*HR-w*HL=s*P) (h' : v'*HR-w'*HL=s*P')
    (hs : s ≠ 0) (hR : HR ≠ 0) (hP : 0 < P) (hP' : 0 < P')
    (hcop : IsCoprime s HR) (hc : IsCoprime P w) (hc' : IsCoprime P' w')
    (hsmall : |frequencyDeterminant v w v' w'| < |s|) :
    v=v' ∧ w=w' ∧ P=P' := by
  have hd := reversal_determinant_zero h h' hcop hsmall
  have heq : P*w' = P'*w := by
    have hz : s*(P*w'-P'*w) = 0 := by
      unfold frequencyDeterminant at hd
      nlinarith [congrArg (fun z : ℤ => z*w') h, congrArg (fun z : ℤ => z*w) h',
        congrArg (fun z : ℤ => z*HR) hd]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hs)
  have hpp := positive_coprime_denominator_unique hP hP' hc hc' heq
  subst P'
  have hww : w=w' := (mul_left_cancel₀ hP.ne' heq).symm
  subst w'
  have hvv : v=v' := by
    apply mul_right_cancel₀ hR
    linarith
  exact ⟨hvv,rfl,rfl⟩
end Ostmann.Characters

end OAI
