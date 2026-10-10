import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # Algebraic identities for nonsingular scalar pullback -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

theorem scalarInfinityPullback_const (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (z : ℂ) :
    scalarInfinityPullback T hT (scalarInfinityConst μ z) = scalarInfinityConst μ z := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT (scalarInfinityConst μ z),
    hT.ae (scalarInfinityConst_ae (μ := μ) z), scalarInfinityConst_ae (μ := μ) z]
    with x hx ht hc
  exact hx.trans (ht.trans hc.symm)

theorem scalarInfinityPullback_mul (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (f g : ScalarLInfinity μ) :
    scalarInfinityPullback T hT (scalarInfinityMul f g) =
      scalarInfinityMul (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT (scalarInfinityMul f g),
    hT.ae (scalarInfinityMul_ae f g),
    scalarInfinityMul_ae (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g),
    scalarInfinityPullback_ae T hT f, scalarInfinityPullback_ae T hT g]
    with x hfg hmul hout hf hg
  rw [hfg, hmul, hout, hf, hg]

theorem scalarInfinityPullback_comp (S T : D → D)
    (hS : Measure.QuasiMeasurePreserving S μ μ) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (f : ScalarLInfinity μ) :
    scalarInfinityPullback S hS (scalarInfinityPullback T hT f) =
      scalarInfinityPullback (T ∘ S) (hT.comp hS) f := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae S hS (scalarInfinityPullback T hT f),
    hS.ae (scalarInfinityPullback_ae T hT f),
    scalarInfinityPullback_ae (T ∘ S) (hT.comp hS) f] with x hs ht hc
  exact hs.trans (ht.trans hc.symm)

theorem scalarInfinityPullback_id (f : ScalarLInfinity μ) :
    scalarInfinityPullback id (Measure.QuasiMeasurePreserving.id μ) f = f := by
  exact Lp.ext (scalarInfinityPullback_ae _ _ _)

end

end KadisonKastler

end OAI
