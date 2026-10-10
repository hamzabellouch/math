import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryGenerator

namespace OAI

/-! # Nondecaying eigenvectors lie in the finite contour range -/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS

theorem stable_projection_fixes_eigenvector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V)
    (hP : IsIdempotentElem P) (hcomm : ∀ t, Commute (S t) P)
    (D δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ t : ℝ≥0, ∀ v, P v = 0 → ‖S t v‖ ≤ D * Real.exp (-δ * (t : ℝ)) * ‖v‖)
    (u : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (he : ∀ t : ℝ≥0, S t u = (Real.exp (lam * (t : ℝ)) : ℂ) • u) : P u = u := by
  let v := u - P u
  have hPv : P v = 0 := by
    have hi := congrArg (fun A : V →L[ℂ] V => A u) hP
    change P (P u) = P u at hi
    simp only [v, map_sub, hi, sub_self]
  have hev (t : ℝ≥0) : S t v = (Real.exp (lam * (t : ℝ)) : ℂ) • v := by
    have hc := congrArg (fun A : V →L[ℂ] V => A u) (hcomm t).eq
    change S t (P u) = P (S t u) at hc
    simp only [v, map_sub, hc, he, map_smul, smul_sub]
  have hlim : Tendsto (fun t : ℝ => D * Real.exp (-δ * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_zero] using tendsto_const_nhds.mul
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hδ)))
  obtain ⟨t, ht, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))).exists
  have hbd := hdecay ⟨t, ht⟩ v hPv
  rw [hev ⟨t, ht⟩, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hbd
  have hlarge : 1 ≤ Real.exp (lam * t) := Real.one_le_exp_iff.mpr (mul_nonneg hlam ht)
  change Real.exp (lam * t) * ‖v‖ ≤ (D * Real.exp (-δ * t)) * ‖v‖ at hbd
  have hv : v = 0 := by
    by_contra hne
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hne
    have hle : ‖v‖ ≤ Real.exp (lam * t) * ‖v‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hlarge hn.le
    have hlt : (D * Real.exp (-δ * t)) * ‖v‖ < ‖v‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall hn
    exact (lt_irrefl ‖v‖) ((hle.trans hbd).trans_lt hlt)
  exact (sub_eq_zero.mp hv).symm

end DefocusingNLS

end OAI
