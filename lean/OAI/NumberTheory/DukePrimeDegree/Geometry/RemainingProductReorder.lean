import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductHolonomy

namespace OAI

/-! # Moving the selected root through the actual remaining product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Function
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma nextConjugation_zero (d : ℕ) (q : InitialRootStep (d+1))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) : q.nextConjugation d 0 w = w := by
  apply Subtype.ext
  simp [nextConjugation]

lemma continuous_conjugationSkew (d : ℕ) (q : InitialRootStep (d+1)) :
    Continuous (fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
      (z.1,q.nextConjugation d z.1 z.2)) := by
  have hU := continuous_rootTransvection q.distinct
  apply continuous_fst.prodMk
  exact (((hU.comp continuous_fst.neg).mul
    (continuous_subtype_val.comp continuous_snd)).mul (hU.comp continuous_fst)).subtype_mk _

def rootBeforeRemaining (d : ℕ) (q : InitialRootStep (d+1))
    (z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root)) : G (d+1) :=
  Matrix.SpecialLinearGroup.transvection q.distinct z.1 * z.2.val

def remainingBeforeRoot (d : ℕ) (q : InitialRootStep (d+1))
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) : G (d+1) :=
  z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2

lemma measurable_rootBeforeRemaining (d : ℕ) (q : InitialRootStep (d+1)) :
    Measurable (q.rootBeforeRemaining d) :=
  ((continuous_rootTransvection q.distinct).comp continuous_fst).measurable.mul
    (continuous_subtype_val.comp continuous_snd).measurable

lemma measurable_remainingBeforeRoot (d : ℕ) (q : InitialRootStep (d+1)) :
    Measurable (q.remainingBeforeRoot d) :=
  (continuous_subtype_val.comp continuous_fst).measurable.mul
    ((continuous_rootTransvection q.distinct).comp continuous_snd).measurable

theorem remainingProduct_reorder (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    [SFinite ν] [SFinite η]
    (h : η = Measure.dirac 0 ∨ ∀ r : ℝ, ν.map (q.nextConjugation d r) = ν) :
    (ν.prod η).map (q.remainingBeforeRoot d) = (η.prod ν).map (q.rootBeforeRemaining d) := by
  have hinv : ∀ᵐ r ∂η, ν.map (q.nextConjugation d r) = ν := by
    rcases h with h | h
    · rw [h]
      have hz : q.nextConjugation d 0 = id := funext (q.nextConjugation_zero d)
      simp [hz]
    · exact Filter.Eventually.of_forall h
  have hS : MeasurePreserving
      (fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
        (z.1,q.nextConjugation d z.1 z.2)) (η.prod ν) (η.prod ν) :=
    (MeasurePreserving.id η).skew_product
      (q.continuous_conjugationSkew d).snd.measurable hinv
  have hp := hS.comp (Measure.measurePreserving_swap (μ := ν) (ν := η))
  have he : q.remainingBeforeRoot d = q.rootBeforeRemaining d ∘
      ((fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
        (z.1,q.nextConjugation d z.1 z.2)) ∘ Prod.swap) := by
    funext z
    change z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2 =
      Matrix.SpecialLinearGroup.transvection q.distinct z.2 *
        (Matrix.SpecialLinearGroup.transvection q.distinct (-z.2) * z.1.val *
          Matrix.SpecialLinearGroup.transvection q.distinct z.2)
    rw [←Matrix.SpecialLinearGroup.transvection_inv]
    group
  rw [he,←Measure.map_map (q.measurable_rootBeforeRemaining d) hp.measurable,hp.map_eq]

end InitialRootStep

theorem ae_intrinsic_remainingProduct_reorder (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ,
      ((q.nextIntrinsicProduct d μ x).prod (intrinsicRootLeaf q.distinct μ x)).map
        (q.remainingBeforeRoot d) =
      ((intrinsicRootLeaf q.distinct μ x).prod (q.nextIntrinsicProduct d μ x)).map
        (q.rootBeforeRemaining d) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hs (p : q.NextRoot) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  have hr := ae_intrinsicRootLeaf_spec q.distinct μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  have halt : ∀ᵐ x ∂μ, intrinsicRootLeaf q.distinct μ x = Measure.dirac 0 ∨
      ∀ r : ℝ, (q.nextIntrinsicProduct d μ x).map (q.nextConjugation d r) =
        q.nextIntrinsicProduct d μ x := by
    rcases intrinsicRootLeaf_ergodic_alternative d q.distinct μ with h | h
    · exact (ae_nextIntrinsicProduct_conjugation d q μ h).mono fun _ hx => Or.inr hx
    · exact h.mono fun _ hx => Or.inl hx
  filter_upwards [ae_all_iff.mpr hs,hr,halt] with x hx hrx ha
  let : ∀ p : q.NextRoot, IsLocallyFiniteMeasure
      (intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x) :=
    fun p => (hx p).1
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf q.distinct μ x) := hrx.1
  let : SFinite (q.nextIntrinsicProduct d μ x) := by
    unfold InitialRootStep.nextIntrinsicProduct
    infer_instance
  exact q.remainingProduct_reorder d _ _ ha

end DukePrimeDegree

end

end OAI
