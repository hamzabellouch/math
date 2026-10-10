import OAI.Geometry.SurfaceImmersion.Atlas.GenericCurvePhases

namespace OAI

/-! Nondegenerate critical points of a restricted phase are isolated, so
only finitely many lie in a compact boundary arc. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry

lemma finite_compact_simple_zeros {f df : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K)
    (hd : ∀ t ∈ K, HasDerivAt f (df t) t)
    (hn : ∀ t ∈ K, f t = 0 → df t ≠ 0) :
    (K ∩ {t | f t = 0}).Finite := by
  apply (hK.inter_right (isClosed_eq hf continuous_const)).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro t ht
  have he : ∀ᶠ s in 𝓝 t, s ≠ t → f s ≠ 0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp ((hd t ht.1).eventually_ne (c := 0) (hn t ht.1 ht.2)))
  obtain ⟨U,hsub,hU,htU⟩ := mem_nhds_iff.mp he
  refine ⟨U,hU,?_⟩
  ext s
  constructor
  · rintro ⟨hsU,hsK,hs0⟩
    apply mem_singleton_iff.mpr
    by_contra hst
    exact hsub hsU hst hs0
  · rintro rfl
    exact ⟨htU,ht⟩

lemma curvePhaseVelocity_hasDerivAt {u v w : ℝ → CurvePlane} {L t : ℝ} {ell : CurvePlane}
    (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t) :
    HasDerivAt (fun s => curvePhaseVelocity u v L s ell)
      (curvePhaseAcceleration u v w L t ell) t := by
  have hu1 : HasDerivAt (fun s => (u s).1) (v t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hu2 : HasDerivAt (fun s => (u s).2) (v t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hv1 : HasDerivAt (fun s => (v s).1) (w t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hv2 : HasDerivAt (fun s => (v s).2) (w t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hh := (((hu1.const_mul L).const_add ell.1).mul hv1).add
    (((hu2.const_mul L).const_add ell.2).mul hv2)
  convert hh using 1
  · rfl
  · dsimp [curvePhaseAcceleration]
    ring

theorem finite_nondegenerate_curve_tangencies
    (u v w : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t)
    (L : ℝ) (ell : CurvePlane) {K : Set ℝ} (hK : IsCompact K)
    (hregular : ∀ t ∈ K, v t ≠ 0)
    (hnondeg : ∀ t, v t ≠ 0 → curvePhaseVelocity u v L t ell = 0 →
      curvePhaseAcceleration u v w L t ell ≠ 0) :
    (K ∩ {t | curvePhaseVelocity u v L t ell = 0}).Finite := by
  apply finite_compact_simple_zeros (df := fun t => curvePhaseAcceleration u v w L t ell)
    (by dsimp [curvePhaseVelocity]; fun_prop) hK
  · intro t _
    exact curvePhaseVelocity_hasDerivAt (hdu t) (hdv t)
  · intro t ht hz
    exact hnondeg t (hregular t ht) hz

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
