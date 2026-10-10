import OAI.Combinatorics.ContingencyTables.Transport.FinitePrefixVariance

namespace OAI

/-! # The finite exposure depth and polynomial coefficient -/

namespace ContingencyTables.FiniteExposureVariance

open scoped Classical

theorem variance_le_polynomial_budget {A : Type*} [Fintype A] {q : ℕ}
    (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) (d U : ℕ) (hq : q ≤ d)
    (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ k : Fin q,prefixContribution w H k ≤ 4*d*((U:ℝ)+1)^6*E) :
    variance w H ≤ 4*(d:ℝ)^2*((U:ℝ)+1)^6*E := by
  have hv := variance_le_prefix_budget w H hw (4*d*((U:ℝ)+1)^6*E) hb
  have hq' : (q:ℝ) ≤ d := by exact_mod_cast hq
  have hcoef : 0 ≤ 4*(d:ℝ)*((U:ℝ)+1)^6 := by positivity
  calc
    _ ≤ q*(4*d*((U:ℝ)+1)^6*E) := hv
    _ ≤ (d:ℝ)*(4*d*((U:ℝ)+1)^6*E) := mul_le_mul_of_nonneg_right hq' (mul_nonneg hcoef hE)
    _ = _ := by ring

end ContingencyTables.FiniteExposureVariance

end OAI
