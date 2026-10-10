import OAI.NumberTheory.DukePrimeDegree.Geometry.RealWindowRebase
import OAI.NumberTheory.DukePrimeDegree.Entropy.ShiftedFactorConditionals

namespace OAI

/-! # The based real leaf of a physical, shifted time window -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma shifted_real_window_rebase
    (ν κ : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (V J : Set ℝ) (hJ : MeasurableSet J) (a t : ℝ)
    (hwindow : (Homeomorph.addRight a) '' J ⊆ V)
    (hκ : κ.map (Homeomorph.addRight a) = ν.restrict V)
    (ht : 0 < (ν.map (Homeomorph.addRight (-a))) (Metric.ball t 1)) :
    ((anchorNormalize κ J).restrict J).map (Homeomorph.addRight (-t)) =
      (anchorNormalize (basedRealMeasure ν (t+a)) (Homeomorph.addRight (-t) '' J)).restrict
        (Homeomorph.addRight (-t) '' J) := by
  let η := ν.map (Homeomorph.addRight (-a))
  let : IsLocallyFiniteMeasure η := translatedRealMeasure_locallyFinite ν (-a)
  have hsymm : (Homeomorph.addRight a).symm = Homeomorph.addRight (-a) := by
    ext x
    rfl
  have hr : η.restrict J = κ.restrict J := by
    simpa only [hsymm] using shifted_leaf_restrict ν κ V J hJ a hwindow hκ
  have hn : (anchorNormalize κ J).restrict J = (anchorNormalize η J).restrict J := by
    rw [←anchorNormalize_restrict_comm κ hJ subset_rfl,
      ←anchorNormalize_restrict_comm η hJ subset_rfl,hr]
  have hη : η = centerRealMeasure ν a := rfl
  have hb : basedRealMeasure η t = basedRealMeasure ν (t+a) := by
    rw [hη,basedRealMeasure_center,add_comm a t]
  rw [hn]
  simpa only [hb] using realWindow_rebase_addRight η t ht J hJ

end DukePrimeDegree

end

end OAI
