import OAI.Combinatorics.ProgressionColoring.HeavyIntervalWidth
import OAI.Combinatorics.ProgressionColoring.LiteralLabelRectangles
import OAI.Combinatorics.ProgressionColoring.LabelFiber

namespace OAI

/-!
# Drift relative to actual heavy adaptive intervals

The heavy multiplicity is counted over `Fin k` using the actual literal full
label. Its natural-index fiber has the same cardinality. Equal labels place the
actual centered representatives in the same half-open interval, providing the
width bound required by the general endpoint argument.
-/

namespace QuantitativeVanDerWaerden

/-- Equal literal labels bound the difference by the actual adaptive interval
width, rather than only by the uniform upper bound on mesh widths. -/
theorem literalFullLabel_second_width (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (hlabel : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |yRep q D lam b i - yRep q D lam a i| ≤
      mesh.width ((literalFullLabel mesh q D lam Ucount hU a).2 i) := by
  have ha := literalFullLabel_second_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_second_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.snd hlabel) i
  rw [← hi] at hb
  unfold AdaptiveMesh.Contains at ha hb
  unfold AdaptiveMesh.width
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

open scoped Classical in
/-- Every heavy literal-label fiber controls the drift relative to the width
of its own adaptive interval in every coordinate. -/
theorem cyclic_heavy_label_relative_width (mesh : AdaptiveMesh)
    {q D lam Ucount k h : ℕ} (hU : 0 < Ucount)
    (a d : CyclicGroup q D) (A v : Fin D → ℝ) (s : Fin D → ℤ) (j : Fin k)
    {M : ℝ} (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M <
      (Finset.univ.filter (fun n : Fin k =>
        literalFullLabel mesh q D lam Ucount hU (a + n.val • d) =
        literalFullLabel mesh q D lam Ucount hU (a + j.val • d))).card)
    (hh : 0 < h)
    (hcongr : ∀ m, m < k → ∀ n, n < k →
      literalFullLabel mesh q D lam Ucount hU (a + m • d) =
        literalFullLabel mesh q D lam Ucount hU (a + n • d) →
      (h : ℤ) ∣ (n : ℤ) - m)
    (hpath : ∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D lam (a + n • d) i - A i -
        (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hdrift : ∀ i, |v i| ≤ 4 * M * mesh.H / (k : ℝ))
    (hsmall : 2 * mesh.H + 4 * M * mesh.H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) *
      mesh.width (mesh.meshLabel (yRep q D lam (a + j.val • d) i)) := by
  classical
  let label := fun n : ℕ => literalFullLabel mesh q D lam Ucount hU (a + n • d)
  have hheavy' : (k : ℝ) / M < (labelFiber k label (label j.val)).card := by
    rw [card_labelFiber]
    convert hheavy using 1; congr
  apply heavy_label_relative_width (j := j.val)
    (fun n => yRep q D lam (a + n • d)) A v s label
    (fun beta i => mesh.width (beta.2 i)) hM hscale hheavy' hh hcongr hpath
  · intro m _ n _ hlabel i
    exact literalFullLabel_second_width mesh q D lam Ucount hU hlabel i
  · intro i
    exact mesh.width_le_two_H _
  · exact hdrift
  · exact hsmall

end QuantitativeVanDerWaerden

end OAI
