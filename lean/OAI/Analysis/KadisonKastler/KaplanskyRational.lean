import OAI.Analysis.KadisonKastler.KaplanskyTransform

namespace OAI

/-! # Resolvent expression and strong continuity of the bounded transform -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

private theorem rational_transform_complex (t : ℝ) :
    (kaplanskyTransform t : ℂ) =
      -(Complex.I - (t : ℂ))⁻¹ - (-Complex.I - (t : ℂ))⁻¹ := by
  have hp : Complex.I - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hm : -Complex.I - (t : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hd : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + t ^ 2 ≠ 0 by positivity)
  unfold kaplanskyTransform
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two resolvents express the bounded real rational transform. -/
theorem kaplanskyTransform_eq_resolvents (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc kaplanskyTransform a = -resolvent a Complex.I - resolvent a (-Complex.I) := by
  rw [cfc_real_eq_complex kaplanskyTransform ha,
    resolvent_eq_cfc_of_selfAdjoint ha (by simp), resolvent_eq_cfc_of_selfAdjoint ha (by simp)]
  have hc (w : ℂ) (hw : w.im ≠ 0) :
      ContinuousOn (fun z : ℂ => (w - z)⁻¹) (spectrum ℂ a) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro z hz he
    have hr := SpectrumRestricts.real_iff.mp ha.spectrumRestricts z hz
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    have hz0 : z.im = 0 := by simpa only [Complex.ofReal_im] using congrArg Complex.im hr
    exact hw (hi.trans hz0)
  rw [← cfc_neg (fun z : ℂ => (Complex.I - z)⁻¹) a,
    ← cfc_sub (fun z : ℂ => -(Complex.I - z)⁻¹)
      (fun z : ℂ => (-Complex.I - z)⁻¹) a (hc Complex.I (by simp)).neg
      (hc (-Complex.I) (by simp))]
  apply cfc_congr
  intro z hz
  have hreal := SpectrumRestricts.real_iff.mp ha.spectrumRestricts z hz
  rw [hreal]
  simpa using rational_transform_complex z.re

/-- Bounded-transform strong continuity requires only self-adjointness,
not a bound on the original net. -/
theorem tendsto_kaplanskyTransform_of_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hT : IsSelfAdjoint T)
    (hlim : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x))) (x : H) :
    Tendsto (fun i => cfc kaplanskyTransform (a i) x) l
      (𝓝 (cfc kaplanskyTransform T x)) := by
  simp only [kaplanskyTransform_eq_resolvents _ (ha _),
    kaplanskyTransform_eq_resolvents _ hT, sub_apply, neg_apply]
  exact (tendsto_resolvent_of_selfAdjoint_strong ha hT hlim (by simp) x).neg.sub
    (tendsto_resolvent_of_selfAdjoint_strong ha hT hlim (by simp) x)

end

end KadisonKastler

end OAI
