import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductFactor
import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationReference

namespace OAI

/-! # Rebasing the actual product of remaining-root coordinates -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma remainingFactor_rebase (d : ℕ) (q : InitialRootStep (d+1))
    (w v : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s t : ℝ) :
    (q.remainingFactor (w,s))⁻¹ * q.remainingFactor (v,t) =
      q.remainingFactor (q.nextConjugation d s (w⁻¹*v),t-s) := by
  apply Subtype.ext
  change (w.val * Matrix.SpecialLinearGroup.transvection q.distinct s)⁻¹ *
      (v.val * Matrix.SpecialLinearGroup.transvection q.distinct t) =
    (Matrix.SpecialLinearGroup.transvection q.distinct (-s) * (w.val⁻¹*v.val) *
      Matrix.SpecialLinearGroup.transvection q.distinct s) *
        Matrix.SpecialLinearGroup.transvection q.distinct (t-s)
  rw [mul_assoc _ (Matrix.SpecialLinearGroup.transvection q.distinct s),
    ←Matrix.SpecialLinearGroup.transvection_add,
    show s+(t-s)=t by ring,←Matrix.SpecialLinearGroup.transvection_inv]
  group

def nextFactorRebase (d : ℕ) (q : InitialRootStep (d+1))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  (Homeomorph.mulLeft w⁻¹).trans (q.nextConjugationHomeomorph d s)

theorem remainingFactor_product_rebase (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    [SFinite ν] [SFinite η]
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s : ℝ) :
    ((ν.prod η).map q.remainingFactor).map (Homeomorph.mulLeft (q.remainingFactor (w,s))⁻¹) =
      ((ν.map (q.nextFactorRebase d w s)).prod (η.map (Homeomorph.addRight (-s)))).map
        q.remainingFactor := by
  rw [Measure.map_map (Homeomorph.mulLeft (q.remainingFactor (w,s))⁻¹).measurable
    q.remainingFactor.measurable,
    Measure.map_prod_map ν η (q.nextFactorRebase d w s).measurable
      (Homeomorph.addRight (-s)).measurable,
    Measure.map_map q.remainingFactor.measurable
      ((q.nextFactorRebase d w s).measurable.prodMap (Homeomorph.addRight (-s)).measurable)]
  apply congrArg (fun f => (ν.prod η).map f)
  funext z
  change (q.remainingFactor (w,s))⁻¹ * q.remainingFactor z =
    q.remainingFactor (q.nextConjugation d s (w⁻¹*z.1),z.2 + -s)
  simpa only [sub_eq_add_neg] using q.remainingFactor_rebase d w z.1 s z.2

lemma nextFactorRebase_reference (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s : ℝ) :
    (((ν.map (q.nextConjugation d (-s))).map (Homeomorph.mulLeft w)).map
      (q.nextFactorRebase d w s)) = ν := by
  rw [Measure.map_map (q.nextFactorRebase d w s).measurable (Homeomorph.mulLeft w).measurable,
    Measure.map_map ((q.nextFactorRebase d w s).measurable.comp
      (Homeomorph.mulLeft w).measurable) (q.continuous_nextConjugation d (-s)).measurable]
  have he : (q.nextFactorRebase d w s ∘ Homeomorph.mulLeft w) ∘ q.nextConjugation d (-s) = id := by
    funext v
    change q.nextConjugation d s (w⁻¹*(w*q.nextConjugation d (-s) v)) = v
    rw [inv_mul_cancel_left,q.nextConjugation_add]
    simpa only [neg_add_cancel] using q.nextConjugation_zero d v
  rw [he,Measure.map_id]

lemma nextFactorRebase_reference_restrict (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s : ℝ)
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hV : MeasurableSet V) :
    ((anchorNormalize
      ((ν.map (q.nextConjugation d (-s))).map (Homeomorph.mulLeft w)) V).restrict V).map
        (q.nextFactorRebase d w s) =
      (anchorNormalize ν (q.nextFactorRebase d w s '' V)).restrict
        (q.nextFactorRebase d w s '' V) := by
  let E := (q.nextFactorRebase d w s).toMeasurableEquiv
  have hEV : MeasurableSet (E '' V) := E.measurableEmbedding.measurableSet_image.mpr hV
  have hn := anchorNormalize_map_equiv
    ((ν.map (q.nextConjugation d (-s))).map (Homeomorph.mulLeft w)) E V
  have hmap : (((ν.map (q.nextConjugation d (-s))).map (Homeomorph.mulLeft w)).map E) = ν :=
    q.nextFactorRebase_reference d ν w s
  change ((anchorNormalize
    ((ν.map (q.nextConjugation d (-s))).map (Homeomorph.mulLeft w)) V).restrict V).map E =
      (anchorNormalize ν (E '' V)).restrict (E '' V)
  conv_rhs => rw [←hmap]
  rw [hn,Measure.restrict_map E.measurable hEV,E.injective.preimage_image]

end InitialRootStep
end DukePrimeDegree

end

end OAI
