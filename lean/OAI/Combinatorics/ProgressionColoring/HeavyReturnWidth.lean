import OAI.Combinatorics.ProgressionColoring.HeavyReturnSeparation
import OAI.Combinatorics.ProgressionColoring.CyclicHeavyIntervalWidth

namespace OAI

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

open scoped Classical in
/-- Every heavy label controls the same actual return displacement, even when
it differs from the label used to select the closest return. -/
theorem every_heavy_relative_width (hq : 0 < q) (hM : 0 < M)
    (hscale : 2 * M ≤ k) (hwidth : 1 / (Ucount : ℝ) ≤ mesh.H)
    (hseparate : 4 * (M : ℝ) * mesh.H < 1)
    (hsmall : 2 * mesh.H + 4 * (M : ℝ) * mesh.H / (h : ℝ) < 1) :
    ∀ r : Fin k,
      (k : ℝ) / (M : ℝ) <
        (Finset.univ.filter (fun n : Fin k =>
          literalFullLabel mesh q D lam Ucount hU (a + n.val • d) =
          literalFullLabel mesh q D lam Ucount hU (a + r.val • d))).card →
      ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
        (2 * (M : ℝ) / (k : ℝ)) *
          mesh.width (mesh.meshLabel (yRep q D lam (a + r.val • d) i)) := by
  classical
  obtain ⟨t, _, _, _, hy⟩ := R.primitive_return_path hq
  have hpath : ∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D lam (a + n • d) i - yRep q D lam a i -
        (n : ℝ) / h * (((lam : ℤ) * t i : ℤ) +
          (yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i) : ℝ) = z := by
    intro n i
    obtain ⟨z, hz⟩ := hy n i
    refine ⟨z, ?_⟩
    simpa only [Int.cast_mul, Int.cast_natCast, R.dilation_eq i, mul_add] using hz
  intro r hr
  apply cyclic_heavy_label_relative_width (M := (M : ℝ)) mesh hU a d (yRep q D lam a)
    (fun i => yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i)
    (fun i => (lam : ℤ) * t i) r
    (by exact_mod_cast hM) (by exact_mod_cast hscale) hr R.gap_pos
    (R.same_label_divides hq hwidth hseparate) hpath R.y_rate hsmall

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
