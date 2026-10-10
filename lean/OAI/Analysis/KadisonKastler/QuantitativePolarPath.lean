import OAI.Analysis.KadisonKastler.SmoothingInverse

namespace OAI

/-! # Quantitative continuous polar paths from two approximate inverses -/

namespace KadisonKastler

noncomputable section

variable {A X : Type*} [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] [TopologicalSpace X]

/-- The smoothing estimates produce a continuous unitary family with
explicit errors in both factors. Only the first family needs continuity. -/
theorem exists_continuous_polar_path (a c : X → A) (ha : Continuous a)
    {r : ℝ} (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hanorm : ∀ x, ‖a x‖ ≤ 1 + r) (hcnorm : ∀ x, ‖c x‖ ≤ 1 + r)
    (hac : ∀ x, ‖a x * c x - 1‖ ≤ r) (hca : ∀ x, ‖c x * a x - 1‖ ≤ r) :
    ∃ v : X → unitary A, Continuous v ∧
      (∀ x, ‖(v x : A) - a x‖ ≤ 4 * r) ∧
      (∀ x, ‖star (v x : A) - c x‖ ≤ 10 * r) := by
  have hr1 : r < 1 := by linarith
  have hinv (x : X) : IsUnit (a x) :=
    isUnit_of_two_approximate_inverses (a x) (c x)
      ((hac x).trans_lt hr1) ((hca x).trans_lt hr1)
  let t (x : X) : Aˣ := (hinv x).unit
  have ht (x : X) : (t x : A) = a x := (hinv x).unit_spec
  have htinverse (x : X) : ‖(((t x)⁻¹ : Aˣ) : A)‖ ≤ (1 + r) / (1 - r) := by
    exact (norm_inverse_le_of_approximate_inverse (t x) (c x) hr1
      (by simpa only [ht] using hac x)).trans
      (div_le_div_of_nonneg_right (hcnorm x) (by linarith))
  have hnum : (1 + r) / (1 - r) ≤ (1 - 4 * r)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [sq_nonneg r]
  have htwo : (1 + r) / (1 - r) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hpolar (x : X) : ‖(polarUnitary (t x) : A) - a x‖ ≤ 4 * r := by
    have hn := norm_polarUnitary_sub_le (t x) (show 0 ≤ 4 * r by positivity)
      (show 4 * r < 1 by linarith)
      (show ‖(t x : A)‖ ≤ 1 + 4 * r by rw [ht]; exact (hanorm x).trans (by linarith))
      ((htinverse x).trans hnum)
    simpa only [ht] using hn
  refine ⟨fun x => polarUnitary (t x), continuous_polarUnitary_of_isUnit a ha hinv,
    hpolar, ?_⟩
  intro x
  have hub := norm_unitary_star_sub_approximate_inverse_le (t x) (polarUnitary (t x))
    (c x) (by simpa only [ht] using hpolar x) (by simpa only [ht] using hac x)
  exact hub.trans (by
    have hn := (htinverse x).trans htwo
    nlinarith)

end

end KadisonKastler

end OAI
