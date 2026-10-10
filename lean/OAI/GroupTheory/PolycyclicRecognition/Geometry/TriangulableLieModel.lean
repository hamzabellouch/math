import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Algebra.Ring.Basic

namespace OAI

/-!
# The published reduction to a real-triangulable Lie model

Y. Cornulier and R. Tessera, *Geometric presentations of Lie groups and
their Dehn functions*, Publications Mathématiques de l'IHÉS 125 (2017),
79–219, Lemma 3.A.1, p.108, gives proper continuous homomorphisms with
cocompact images `G ← G₁ → G₂ ← G₃`, with `G₃` real triangulable.
Definition 1.1, p.83, identifies this last property with being isomorphic
to a closed connected group of invertible upper triangular real matrices.

The input below keeps precisely that topological reduction. Its metric
consequence is proved using the separately identified compatible-metric
existence input and the explicit inverse-map composition lemmas. No
adjoint basis, height control, or recognition conclusion is placed in the
published input.
-/

noncomputable section

namespace PolycyclicRecognition

/-- The actual closed triangular matrix realization from CT Definition 1.1. -/
def IsRealTriangulable (S : SimplyConnectedSolvableLieModel) : Prop :=
  ∃ (n : ℕ) (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ),
    Topology.IsClosedEmbedding ρ ∧
      ∀ g, (ρ g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular

/-- Only the locally compact group data used from an intermediate Lie
group in the CT reduction; the smooth structure is unnecessary here. -/
structure CompactlyGeneratedLCModel where
  carrier : Type
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]
  [t2Space : T2Space carrier]
  [locallyCompactSpace : LocallyCompactSpace carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  compactlyGenerated : ∃ K : Set carrier, IsCompact K ∧ Subgroup.closure K = ⊤

attribute [instance] CompactlyGeneratedLCModel.group CompactlyGeneratedLCModel.topologicalSpace
  CompactlyGeneratedLCModel.topologicalGroup CompactlyGeneratedLCModel.t2Space
  CompactlyGeneratedLCModel.locallyCompactSpace CompactlyGeneratedLCModel.secondCountableTopology

/-- A proper continuous homomorphism whose image has a compact coset
cover, the cocompactness condition in the CT arrows. -/
structure ProperCocompactHom (A B : Type*) [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] where
  hom : A →* B
  proper : IsProperMap hom
  cover : ∃ K : Set B, IsCompact K ∧
    ∀ b : B, ∃ (a : A) (k : B), k ∈ K ∧ hom a * k = b

/-- The solvable-source specialization of CT Lemma 3.A.1. The intermediate
Lie groups are retained only through the locally compact data needed to
compare their metrics. -/
def CornulierTesseraModelInput : Prop :=
  ∀ S : SimplyConnectedSolvableLieModel,
    ∃ T : SimplyConnectedSolvableLieModel, IsRealTriangulable T ∧
      ∃ G₁ G₂ : CompactlyGeneratedLCModel,
        Nonempty (ProperCocompactHom G₁.carrier S.carrier) ∧
        Nonempty (ProperCocompactHom G₁.carrier G₂.carrier) ∧
        Nonempty (ProperCocompactHom T.carrier G₂.carrier)

/-- Compatible metrics turn one of the topological arrows into actual
coarse inverse maps. -/
theorem ProperCocompactHom.nonempty_metricQuasiEquivalence
    {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    (f : ProperCocompactHom A B) (dA : ProperChainMetric A) (dB : ProperChainMetric B) :
    letI := dA.compatibleMetric
    letI := dB.compatibleMetric
    Nonempty (MetricQuasiEquivalence A B) := by
  let := dA.compatibleMetric
  let := dB.compatibleMetric
  let := dA.proper_compatibleMetric
  let := dB.proper_compatibleMetric
  let := dA.isometric_compatibleMetric
  let := dB.isometric_compatibleMetric
  obtain ⟨K, hK, hcover⟩ := f.cover
  exact nonempty_metricQuasiEquivalence_of_proper_cocompact_hom
    dA.chains_compatibleMetric dB.chains_compatibleMetric
    f.hom f.proper.continuous f.proper K hK hcover

/-- The metric reduction follows from the precise topological CT input:
choose compatible metrics and compose the three arrows with their actual
coarse inverses. -/
theorem exists_realTriangulable_metric_model
    (ct : CornulierTesseraModelInput) (metricInput : GeodesicMetricExistenceInput)
    (S : SimplyConnectedSolvableLieModel) :
    ∃ T : SimplyConnectedSolvableLieModel, IsRealTriangulable T ∧
      ∃ (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier),
        letI := dS.compatibleMetric
        letI := dT.compatibleMetric
        Nonempty (MetricQuasiEquivalence S.carrier T.carrier) := by
  obtain ⟨T, hT, G₁, G₂, ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ := ct S
  obtain ⟨dS⟩ := S.nonempty_properChainMetric metricInput
  obtain ⟨dT⟩ := T.nonempty_properChainMetric metricInput
  obtain ⟨d₁⟩ := metricInput G₁.carrier G₁.compactlyGenerated
  obtain ⟨d₂⟩ := metricInput G₂.carrier G₂.compactlyGenerated
  refine ⟨T, hT, dS, dT, ?_⟩
  let := dS.compatibleMetric
  let := dT.compatibleMetric
  let := d₁.compatibleMetric
  let := d₂.compatibleMetric
  obtain ⟨e₁⟩ := f₁.nonempty_metricQuasiEquivalence d₁ dS
  obtain ⟨e₂⟩ := f₂.nonempty_metricQuasiEquivalence d₁ d₂
  obtain ⟨e₃⟩ := f₃.nonempty_metricQuasiEquivalence dT d₂
  exact ⟨(e₁.symm.trans e₂).trans e₃.symm⟩

end PolycyclicRecognition

end

end OAI
