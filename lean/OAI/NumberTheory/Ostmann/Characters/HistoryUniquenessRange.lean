import OAI.NumberTheory.Ostmann.Characters.HistoryUniqueness

namespace OAI

namespace Ostmann.Characters

theorem reversal_unique_of_range {v w v' w' P P' s HL HR B V:ℤ}
    (h : v*HR-w*HL=s*P) (h' : v'*HR-w'*HL=s*P')
    (hs:s≠0) (hR:0<HR) (hP:0<P) (hP':0<P')
    (hPB:P≤B) (hPB':P'≤B) (hw:|w|≤V) (hw':|w'|≤V)
    (hgap:2*B*V<HR) (hcop:IsCoprime s HR)
    (hc:IsCoprime P w) (hc':IsCoprime P' w') : v=v' ∧ w=w' ∧ P=P' := by
  have hB : 0≤B := hP.le.trans hPB
  have hV : 0≤V := (abs_nonneg w).trans hw
  have hid : HR*frequencyDeterminant v w v' w'=s*(P*w'-P'*w) := by
    unfold frequencyDeterminant
    linear_combination w'*h-w*h'
  have habs := congrArg abs hid
  rw [abs_mul,abs_of_pos hR,abs_mul] at habs
  have hcross : |P*w'-P'*w|≤2*B*V := by
    calc
      _ ≤ |P*w'|+|P'*w| := abs_sub _ _
      _ = P*|w'|+P'*|w| := by rw [abs_mul,abs_mul,abs_of_pos hP,abs_of_pos hP']
      _ ≤ B*V+B*V := add_le_add
        (mul_le_mul hPB hw' (abs_nonneg _) hB)
        (mul_le_mul hPB' hw (abs_nonneg _) hB)
      _ = _ := by ring
  have hsmall : |frequencyDeterminant v w v' w'| < |s| := by
    have hh := (mul_le_mul_of_nonneg_left hcross (abs_nonneg s)).trans_lt
      (mul_lt_mul_of_pos_left hgap (abs_pos.mpr hs))
    rw [← habs] at hh
    nlinarith
  exact reversal_unique h h' hs hR.ne' hP hP' hcop hc hc' hsmall

end Ostmann.Characters

end OAI
