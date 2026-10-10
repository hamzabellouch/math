import OAI.Analysis.KadisonKastler.ScalarPositiveLimit

namespace OAI

/-! # Swapping the two probability coordinates on scalar classes -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]

def scalarProductSwapL : ScalarLInfinity (μ.prod μ) →L[ℂ] ScalarLInfinity (μ.prod μ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Prod.swap
    (Measure.measurePreserving_swap (μ := μ) (ν := μ))).toContinuousLinearMap

theorem scalarProductSwapL_ae (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL f =ᵐ[μ.prod μ] fun z => f z.swap :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_swap (μ := μ) (ν := μ))

theorem scalarProductSwapL_norm (f : ScalarLInfinity (μ.prod μ)) :
    ‖scalarProductSwapL f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (Measure.measurePreserving_swap (μ := μ) (ν := μ))

theorem scalarProductSwapL_involution (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarProductSwapL f) = f := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarProductSwapL_ae f)
  filter_upwards [scalarProductSwapL_ae (scalarProductSwapL f), hp] with z hz hp
  exact hz.trans hp

theorem scalarProductSwapL_const (z : ℂ) :
    scalarProductSwapL (scalarInfinityConst (μ.prod μ) z) = scalarInfinityConst (μ.prod μ) z := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityConst_ae (μ := μ.prod μ) z)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityConst _ z), hp,
    scalarInfinityConst_ae (μ := μ.prod μ) z] with x hx hp hc
  exact hx.trans (hp.trans hc.symm)

theorem scalarProductSwapL_mul (f g : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarInfinityMul f g) =
      scalarInfinityMul (scalarProductSwapL f) (scalarProductSwapL g) := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityMul f g), hp,
    scalarProductSwapL_ae f, scalarProductSwapL_ae g,
    scalarInfinityMul_ae (scalarProductSwapL f) (scalarProductSwapL g)] with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

theorem scalarProductSwapL_positive (f : ScalarLInfinity (μ.prod μ))
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarProductSwapL f) := by
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hf
  filter_upwards [scalarProductSwapL_ae f, hp] with x hx hp
  rwa [hx]

theorem scalarProductSwapL_intertwine
    (T U : D × D → D × D)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod μ) (μ.prod μ))
    (hU : Measure.QuasiMeasurePreserving U (μ.prod μ) (μ.prod μ))
    (hcomm : ∀ z, T z.swap = (U z).swap) (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarInfinityPullback T hT f) =
      scalarInfinityPullback U hU (scalarProductSwapL f) := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae T hT f)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityPullback T hT f), hp,
    scalarInfinityPullback_ae U hU (scalarProductSwapL f), hU.ae (scalarProductSwapL_ae f)]
    with z ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

end

end KadisonKastler

end OAI
