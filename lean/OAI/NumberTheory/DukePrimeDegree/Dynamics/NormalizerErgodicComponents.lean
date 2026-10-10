import OAI.NumberTheory.DukePrimeDegree.Dynamics.NormalizedDenseSubgroup
import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizerKernelCovariance

namespace OAI

/-!
# Actual ergodic components covariant under a normalizer

The countable dense subgroup is chosen closed under all conjugates by
one specified normalizer. The resulting conditional kernel consists of
ergodic components for the full subgroup, and transforms covariantly
under that normalizer. Individual components are not assumed fixed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_subgroup_normalizer_ergodic_decomposition {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (haμ : μ.map (fun x => rightAction x a) = μ) :
    ∃ (m : MeasurableSpace (X n)) (hm : m ≤ xMeasurableSpace n),
      letI : MeasurableSpace (X n) := xMeasurableSpace n
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      @MeasurePreserving (X n) (X n) m m (fun x => rightAction x a)
        (μ.trim hm) (μ.trim hm) ∧
      (∀ᵐ z ∂μ.trim hm, ErgodicSMul H (X n) (condExpKernel μ m z)) ∧
      ∀ᵐ z ∂μ.trim hm,
        (condExpKernel μ m z).map (fun x => rightAction x a) =
          condExpKernel μ m (rightAction z a) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨S, hSH, hcount, hdense, haS⟩ :=
    exists_countable_dense_normalized_subgroup H a ha
  let : Countable S := hcount
  let φ : S →* H := S.inclusion hSH
  have hdφ : DenseRange φ := hdense
  have hpS (s : S) : MeasurePreserving (fun x : X n => s • x) μ μ :=
    latticeSubgroup_preserving S μ (hSH.trans hH) s
  obtain ⟨hdec, hcomponents⟩ := action_ergodic_decomposition μ hpS
  let m := actionInvariantSigma S (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le S (X n)
  refine ⟨m, hm, hdec, lattice_normalizer_preserves_invariantSigma S a haS μ haμ,
    ?_, lattice_normalizer_component_covariance S a haS μ haμ⟩
  filter_upwards [hcomponents] with z hz
  let ν := condExpKernel μ m z
  let : ErgodicSMul S (X n) ν := hz
  have hpSν (s : S) : MeasurePreserving (fun x : X n => φ s • x) ν ν := by
    change MeasurePreserving (fun x : X n => s • x) ν ν
    exact measurePreserving_smul s ν
  have hpHν (h : H) : MeasurePreserving (fun x : X n => h • x) ν ν :=
    preserving_of_dense_action φ hdφ ν hpSν h
  refine {
    measure_preimage_smul := ?_
    aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro h B hB
    exact (hpHν h).measure_preimage hB.nullMeasurableSet
  · intro B hB hfix
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := S) hB
    intro s
    exact hfix (φ s)

end DukePrimeDegree

end

end OAI
