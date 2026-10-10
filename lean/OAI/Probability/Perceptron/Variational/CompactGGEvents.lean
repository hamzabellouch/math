import Mathlib
import OAI.Probability.Perceptron.Variational.TripleIndex
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma compactGG_events (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock CompactJointOverlap n →ᵇ ℝ) (g : CompactJointOverlap →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock CompactJointOverlap n)) (hs : MeasurableSet s)
    (t : Set CompactJointOverlap) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock CompactJointOverlap n × CompactJointOverlap) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=CompactJointOverlap) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray CompactJointOverlap => Q i j) := by fun_prop
  rw [map_measureReal_apply (hb.prodMk (hm _ _)) (hs.prod ht),
    measureReal_nnreal_smul_apply,measureReal_add_apply] at he
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (μ : Measure _).map (fun Q => (compactBlock n Q,Q i j))).real (s×ˢt) =
      ∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}) := by
    simp only [measureReal_def,Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (by intro _ _; finiteness)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_apply (hb.prodMk (hm _ _)) (hs.prod ht)]
    rfl
  rw [hsum] at he
  have hprod : (((μ : Measure _).map (compactBlock n)).prod
      ((μ : Measure _).map (fun Q : CompactArray CompactJointOverlap => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

def compactPairReal (x : CompactJointOverlap) : ℝ×ℝ := (x.1.val,x.2.val)
def compactArrayReal (Q : CompactArray CompactJointOverlap) : PairedOverlapArray :=
  fun i j => compactPairReal (Q i j)
def compactBlockReal {n : ℕ} (Q : CompactBlock CompactJointOverlap n) : PairedOverlapBlock n :=
  fun i j => compactPairReal (Q i j)

lemma compactPairReal_measurable : Measurable compactPairReal := by unfold compactPairReal; fun_prop
lemma compactArrayReal_measurable : Measurable compactArrayReal := by
  unfold compactArrayReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))
lemma compactBlockReal_measurable (n : ℕ) : Measurable (compactBlockReal (n:=n)) := by
  unfold compactBlockReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))

def compactRealLaw (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    Measure PairedOverlapArray := (μ : Measure _).map compactArrayReal

instance compactRealLaw_probability (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactRealLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff compactArrayReal_measurable.aemeasurable).2 inferInstance

lemma compactRealLaw_gg (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0) :
    JointGhirlandaGuerra (compactRealLaw μ) := by
  intro n hn i s hs t ht
  have hb : Measurable (pairedBlock n) := by unfold pairedBlock; fun_prop
  have hedge (a b : ℕ) : Measurable (fun Q : PairedOverlapArray => Q a b) := by fun_prop
  have hmap (u : Set PairedOverlapArray) (hu : MeasurableSet u) :
      (compactRealLaw μ).real u=(μ : Measure _).real (compactArrayReal ⁻¹' u) :=
    map_measureReal_apply compactArrayReal_measurable hu
  rw [hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i n∈t}) ((hs.preimage hb).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hb), hmap {Q | Q 0 1∈t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i j∈t})
    ((hs.preimage hb).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact compactGG_events μ n (by omega) i (hGG n i)
    (compactBlockReal ⁻¹' s) (hs.preimage (compactBlockReal_measurable n))
    (compactPairReal ⁻¹' t) (ht.preimage compactPairReal_measurable)

lemma compactRealLaw_exchangeable (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _)) :
    PairedSwapInvariant (compactRealLaw μ) := by
  intro i j
  have hp : Measurable (pairedRelabel (Equiv.swap i j)) := by unfold pairedRelabel; fun_prop
  refine ⟨hp,?_⟩
  unfold compactRealLaw
  rw [Measure.map_map hp compactArrayReal_measurable]
  change Measure.map (compactArrayReal ∘ compactRelabel (Equiv.swap i j)) _ = _
  rw [← Measure.map_map compactArrayReal_measurable (hEx _).measurable,(hEx _).map_eq]

lemma compactRealLaw_gram (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q))) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.snd Q))) := by
  constructor
  · exact ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst)) |>.mpr hR
  · exact ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_snd)) |>.mpr hT

lemma compactRealLaw_diagonals (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).1≤1) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).2≤1) := by
  constructor
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).1.property.2)
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).2.property.2)

lemma compact_gg_no_crossing (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val) := by
  obtain ⟨hgr,hgt⟩ := compactRealLaw_gram μ hR hT
  obtain ⟨hdr,hdt⟩ := compactRealLaw_diagonals μ
  have hh := joint_gg_no_crossing (compactRealLaw μ) (compactRealLaw_exchangeable μ hEx)
    (compactRealLaw_gg μ hGG) hgr hgt hdr hdt
  exact (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mp hh

end SphericalPerceptronFreeEnergy

end

end OAI
