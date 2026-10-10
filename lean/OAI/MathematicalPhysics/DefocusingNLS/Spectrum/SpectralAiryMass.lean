import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryMomentum

namespace OAI

/-! A positive lower bound for the Airy mass after the momentum turns positive. -/

open Set
namespace DefocusingNLS

theorem spectralScalarMass_pos (q : ℂ × ℂ) (hJ : spectralScalarFlux q≠0) :
    0<spectralScalarMass q := by
  rw [spectralScalarMass,Complex.normSq_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (spectralScalarFlux_ne_zero_value q hJ))

theorem spectralAiry_eventual_mass_bound
    (q : ℝ → ℂ × ℂ) (T : ℝ) (hT : 1≤T)
    (hq : ContinuousOn q (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hJ : spectralScalarFlux (q T)≠0) :
    ∃ S : ℝ, T≤S ∧ 0<spectralScalarMass (q S) ∧
      ∀ t, S≤t → 0<spectralScalarMomentum (q t) ∧ spectralScalarMass (q S)≤ spectralScalarMass (q t) := by
  obtain ⟨S,hTS,hP⟩ := spectralAiry_eventually_positive_momentum q T hT hq hD hJ
  have hJs : spectralScalarFlux (q S)≠0 := by
    rw [spectralScalarFlux_const T S q (fun x => -x) (hq.mono (fun _ hx => hx.1))
      (fun x hx => by simpa only [Complex.ofReal_neg] using hD x hx.1.le) S ⟨hTS,le_rfl⟩]
    exact hJ
  refine ⟨S,hTS,spectralScalarMass_pos (q S) hJs,?_⟩
  have hc : ContinuousOn (fun t => spectralScalarMass (q t)) (Ici S) := by
    have hh := ((hq.mono (Ici_subset_Ici.mpr hTS)).fst.norm.pow 2)
    change ContinuousOn (fun t => ‖(q t).1‖^2) (Ici S) at hh
    simpa only [spectralScalarMass,Complex.normSq_eq_norm_sq] using hh
  have hm : MonotoneOn (fun t => spectralScalarMass (q t)) (Ici S) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici S) hc
    · intro t ht
      have htS : S<t := by simpa only [interior_Ici,mem_Ioi] using ht
      exact (spectralScalarMass_hasDerivAt q (-(t : ℂ)) t (hD t (hTS.trans htS.le))).differentiableAt.differentiableWithinAt
    · intro t ht
      have htS : S<t := by simpa only [interior_Ici,mem_Ioi] using ht
      rw [(spectralScalarMass_hasDerivAt q (-(t : ℂ)) t (hD t (hTS.trans htS.le))).deriv]
      exact mul_nonneg (by norm_num) (hP t htS.le).le
  intro t ht
  exact ⟨hP t ht,hm (by simp only [mem_Ici,le_refl]) (by simpa only [mem_Ici] using ht) ht⟩

end DefocusingNLS

end OAI
