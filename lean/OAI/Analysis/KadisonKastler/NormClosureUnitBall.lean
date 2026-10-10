import OAI.Analysis.KadisonKastler.PublishedKaplansky

namespace OAI

/-! # Unit balls and norm closure of a star subalgebra

Radial rescaling of a norm approximant preserves algebra membership and
costs at most a second copy of the approximation error.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normClosure_unitBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {b : H →L[ℂ] H}
    (hb : b ∈ A.topologicalClosure) (hbn : ‖b‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖(a : H →L[ℂ] H)‖ ≤ 1 ∧ ‖b - (a : H →L[ℂ] H)‖ < ε := by
  change b ∈ closure (A : Set (H →L[ℂ] H)) at hb
  obtain ⟨c, hc, hcb⟩ := Metric.mem_closure_iff.mp hb (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hcb
  by_cases hcn : ‖c‖ ≤ 1
  · exact ⟨⟨c, hc⟩, hcn, by linarith⟩
  have hcpos : 0 < ‖c‖ := by linarith
  have hcone : 1 ≤ ‖c‖ := le_of_not_ge hcn
  let a : A := ⟨((‖c‖⁻¹ : ℝ) : ℂ) • c, A.smul_mem hc _⟩
  have han : ‖(a : H →L[ℂ] H)‖ = 1 := by
    change ‖((‖c‖⁻¹ : ℝ) : ℂ) • c‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hcpos.le), inv_mul_cancel₀ hcpos.ne']
  have hac : ‖(a : H →L[ℂ] H) - c‖ = ‖c‖ - 1 := by
    change ‖((‖c‖⁻¹ : ℝ) : ℂ) • c - c‖ = ‖c‖ - 1
    rw [Complex.coe_smul]
    rw [show (‖c‖⁻¹ : ℝ) • c - c = (‖c‖⁻¹ - 1) • c by
      rw [sub_smul, one_smul]]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ((inv_le_one₀ hcpos).mpr hcone)), neg_sub,
      sub_mul, one_mul, inv_mul_cancel₀ hcpos.ne']
  have hdiff : ‖c‖ - 1 ≤ ‖b - c‖ := by
    have htriangle : ‖c‖ ≤ ‖c - b‖ + ‖b‖ := norm_le_norm_sub_add c b
    rw [norm_sub_rev c b] at htriangle
    linarith
  refine ⟨a, han.le, ?_⟩
  have htriangle : ‖b - (a : H →L[ℂ] H)‖ ≤ ‖b - c‖ + ‖c - (a : H →L[ℂ] H)‖ := by
    simpa only [dist_eq_norm] using dist_triangle b c (a : H →L[ℂ] H)
  rw [norm_sub_rev c (a : H →L[ℂ] H), hac] at htriangle
  linarith

end

end KadisonKastler

end OAI
