import OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport

namespace OAI

/-! # Eliminating the actual auxiliary-defect coefficient

Conditional repair bounds each auxiliary defect fibre by one endpoint
child. The elementary reciprocal calculation below converts their sum
into the manuscript's uniform adjacent-mean transport constant.
-/

namespace ContingencyTables.IntegerWeightedTransport

lemma root_coefficient_bound (s t K c d : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hK : 0 ≤ K) (hc : c ≤ d*max s t) :
    min s t*(1/s+1/t+K*c/(s*t)) ≤ 2+K*d := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (by simpa only [max_comm] using hc) (le_of_not_ge hst)
    simpa only [min_comm,mul_comm t s,add_comm (1/t) (1/s)] using h
  rw [min_eq_left hst,max_eq_right hst] at *
  have he : s*(1/s+1/t+K*c/(s*t))=1+s/t+K*(c/t) := by
    field_simp
  rw [he]
  have hst' : s/t ≤ 1 := (div_le_one ht).mpr hst
  have hc' : c/t ≤ d := (div_le_iff₀ ht).mpr hc
  have hkc := mul_le_mul_of_nonneg_left hc' hK
  linarith

/-- The hard root transport and the proved repair domination give the
uniform adjacent-mean estimate used in exposure variance. -/
theorem repaired_root_transport (s t c d W E Δ : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hE : 0 ≤ E)
    (hc : c ≤ d*max s t)
    (htransport : Δ^2 ≤ (1/s+1/t+2*(W+1)^2*c/(s*t))*E) :
    min s t*Δ^2 ≤ (2+2*d*(W+1)^2)*E := by
  have hcoef := root_coefficient_bound s t (2*(W+1)^2) c d hs ht (by positivity) hc
  calc
    _ ≤ min s t*((1/s+1/t+2*(W+1)^2*c/(s*t))*E) :=
      mul_le_mul_of_nonneg_left htransport (le_min hs.le ht.le)
    _ = (min s t*(1/s+1/t+2*(W+1)^2*c/(s*t)))*E := by ring
    _ ≤ (2+(2*(W+1)^2)*d)*E := mul_le_mul_of_nonneg_right hcoef hE
    _ = _ := by ring

end ContingencyTables.IntegerWeightedTransport

end OAI
