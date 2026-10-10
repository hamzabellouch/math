import OAI.Combinatorics.ProgressionColoring.HeavyLabelReturn
import OAI.Combinatorics.ProgressionColoring.RationalSeparation

namespace OAI

/-!
# Every label lies in one residue class of the closest return

The primitive rational path of an actual heavy-label return separates distinct
residues even after its small real drift. The literal uniform interval width
therefore forces every full-label fiber, including all other heavy fibers, to
lie in a single residue class of this same denominator.
-/

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

/-- One actual closest return supplies the common residue-class property for
every literal full label on the progression. -/
theorem same_label_divides (hq : 0 < q)
    (hwidth : 1 / (Ucount : ℝ) ≤ mesh.H)
    (hsmall : 4 * (M : ℝ) * mesh.H < 1) :
    ∀ m, m < k → ∀ n, n < k →
      literalFullLabel mesh q D lam Ucount hU (a + m • d) =
        literalFullLabel mesh q D lam Ucount hU (a + n • d) →
      (h : ℤ) ∣ (n : ℤ) - m := by
  obtain ⟨t, _, hp, hx, _⟩ := R.primitive_return_path hq
  have hk : 0 < k := by have := R.end_lt; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hperiod : (h : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast R.gap_le
  have hmargin := return_separation_margin R.gap_pos hperiod
    (by positivity : (0 : ℝ) ≤ 1 / (Ucount : ℝ)) hwidth hsmall
  have hdrift (i : Fin D) : (k : ℝ) *
      |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
      2 * (M : ℝ) * (1 / (Ucount : ℝ)) := by
    have hr := (le_div_iff₀ hkR).mp (R.x_rate i)
    simpa only [mul_comm] using hr
  intro m hm n hn heq
  exact same_label_divisible_index_difference
    (fun z => xRep q D (a + z • d)) (xRep q D a)
    (fun i => xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)
    (fun z => literalFullLabel mesh q D lam Ucount hU (a + z • d))
    R.gap_pos hp (fun z _ i => hx z i) hdrift hmargin
    (fun z _ w _ hzw i => literalFullLabel_same_first_distance
      mesh q D lam Ucount hU hzw i) hn hm heq.symm

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
