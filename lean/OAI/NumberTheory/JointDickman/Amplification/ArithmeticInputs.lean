import OAI.NumberTheory.JointDickman.Arithmetic.RoughConvolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OAI

/-!
# Published arithmetic inputs at the strength needed here

The fixed-order Selberg–Delange expansion is Granville–Koukoulopoulos,
*Beyond the LSD method* (2019), Theorem 1, specialized to
`μ²(n) z^ω(n)`, or Koukoulopoulos, *The Distribution of Prime Numbers*,
Theorem 13.2. The expansion concerns squarefree weights and contains no
character estimates.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def squarefreeSummatory (z Y : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, squarefreeWeight z n

/-- The convergent Euler-product normalization of the first LSD coefficient. -/
noncomputable def squarefreeLeadingConstant (z : ℝ) : ℝ :=
  (∏' p : {p : ℕ // p.Prime},
    (1 + z / (p.val : ℝ)) * (1 - 1 / (p.val : ℝ)) ^ z) / Real.Gamma z

namespace PublishedInputs

/-- Only the two positive exponents used by the paper, with all fixed
expansion orders and the actual leading coefficient. -/
def SquarefreeSelbergDelangeInput : Prop :=
  ∀ z : ℝ, z = 1 / 4 ∨ z = 1 / 2 →
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 3 ≤ Y →
        |squarefreeSummatory z Y -
          Y * ∑ j ∈ range (H + 1), c j * (Real.log Y) ^ (z - 1 - j)| ≤
            C * Y * (Real.log Y) ^ (z - 2 - H)

/-- The classical reciprocal-prime Mertens estimate, at its usual
`O(1/log x)` strength: Montgomery–Vaughan, Multiplicative Number Theory I,
Theorem 2.7(d). -/
def PrimeReciprocalMertensInput : Prop :=
  ∃ M C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
      Real.log (Real.log x) - M| ≤ C / Real.log x

/-- Mertens' product theorem, with its normalized limiting constant:
Montgomery–Vaughan, Multiplicative Number Theory I, Theorem 2.7(e). -/
def PrimeProductMertensInput : Prop :=
  Tendsto (fun x : ℝ => Real.log x *
    ∏ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)))
    atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

end PublishedInputs

/-- The fixed-order expansion in particular supplies the leading term with
one full logarithmic saving, with no uniformity in an unbounded order. -/
theorem squarefreeSummatory_one_term
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 3 ≤ Y →
      |squarefreeSummatory z Y -
        Y * squarefreeLeadingConstant z * (Real.log Y) ^ (z - 1)| ≤
          C * Y * (Real.log Y) ^ (z - 2) := by
  obtain ⟨c, hc, _, horders⟩ := hSD z hz
  obtain ⟨C, hC, hbound⟩ := horders 0
  refine ⟨C, hC, fun Y hY => ?_⟩
  simpa [hc, mul_assoc] using hbound Y hY

/-- The leading normalized asymptotic, proved from the cited expansion. -/
theorem squarefreeSummatory_normalized_tendsto
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    Tendsto (fun Y : ℝ => squarefreeSummatory z Y /
      (Y * (Real.log Y) ^ (z - 1))) atTop (𝓝 (squarefreeLeadingConstant z)) := by
  obtain ⟨C, _, hbound⟩ := squarefreeSummatory_one_term hSD hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun Y : ℝ => C / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with Y hY
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hp : 0 < (Real.log Y) ^ (z - 1) := Real.rpow_pos_of_pos hlog _
  have hden : 0 < Y * (Real.log Y) ^ (z - 1) := mul_pos hY0 hp
  have hexp : (Real.log Y) ^ (z - 2) = (Real.log Y) ^ (z - 1) / Real.log Y := by
    rw [show z - 2 = (z - 1) - 1 by ring, Real.rpow_sub_one hlog.ne']
  rw [Real.norm_eq_abs]
  have heq : |squarefreeSummatory z Y / (Y * (Real.log Y) ^ (z - 1)) -
      squarefreeLeadingConstant z| =
      |squarefreeSummatory z Y - Y * squarefreeLeadingConstant z * (Real.log Y) ^ (z - 1)| /
        (Y * (Real.log Y) ^ (z - 1)) := by
    calc
      _ = |(squarefreeSummatory z Y - Y * squarefreeLeadingConstant z *
          (Real.log Y) ^ (z - 1)) / (Y * (Real.log Y) ^ (z - 1))| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_div, abs_of_pos hden]
  rw [heq]
  calc
    _ ≤ (C * Y * (Real.log Y) ^ (z - 2)) / (Y * (Real.log Y) ^ (z - 1)) :=
      div_le_div_of_nonneg_right (hbound Y hY) hden.le
    _ = C / Real.log Y := by
      rw [hexp]
      field_simp

end JointDickman

end OAI
