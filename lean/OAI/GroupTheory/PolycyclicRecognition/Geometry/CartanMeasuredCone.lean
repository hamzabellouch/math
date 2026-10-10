import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealGroup
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeKernelHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionHaar

namespace OAI

/-! # The actual ideal, quotient and Haar measures for a fixed cone -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- Exponential and group maps for the one fixed mixed-word ideal. -/
structure ConeGroupMaps
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (I : NilpotentLieModel (M.coneWordIdeal C)) where
  expQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier
  expI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier
  isExpQ : IsGroupExponential expQ
  isExpI : IsGroupExponential expI
  chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier
  chartI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier ≃ₜ I.carrier
  chartQ_eq : ∀ v, chartQ v = expQ v
  chartI_eq : ∀ v, chartI v = expI v
  quotient : F.N.carrier →* Q.carrier
  quotient_continuous : Continuous quotient
  sectionMap : ContinuousMap Q.carrier F.N.carrier
  section_rightInverse : ∀ q, quotient (sectionMap q) = q
  kernel_eq : (quotient.ker : Set F.N.carrier) = F.ExpN ''
    (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H)))
  quotient_exp : ∀ v, quotient (F.ExpN (F.N.equiv v)) =
    expQ (Q.equiv (M.coneProjection C v))
  inclusion : I.carrier →* F.N.carrier
  inclusion_closed : Topology.IsClosedEmbedding inclusion
  inclusion_exp : ∀ v : M.coneWordIdeal C,
    inclusion (expI (I.equiv v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H))
  inclusion_range : range inclusion = (quotient.ker : Set F.N.carrier)

/-- Compatible Haar data; no profile, metric bound or offset is included. -/
structure ConeGroupMeasures
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (I : NilpotentLieModel (M.coneWordIdeal C)) (D : M.ConeGroupMaps F C Q I) where
  measureQ : Measure Q.carrier
  measureI : Measure I.carrier
  haarQ : measureQ.IsHaarMeasure
  haarI : measureI.IsHaarMeasure
  haarKernel : (Measure.map
    (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI).IsHaarMeasure
  conjugation_invariant : ∀ n : F.N.carrier,
    MeasurePreserving (quotientKernelConjugate D.quotient n)
      (Measure.map (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI)
      (Measure.map (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI)
  kernel_rightInvariant : (Measure.map
    (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI).IsMulRightInvariant

/-- The concrete groups, maps and compatible measures for one cone. -/
structure MeasuredCone where
  Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  I : NilpotentLieModel (M.coneWordIdeal C)
  maps : M.ConeGroupMaps F C Q I
  measures : M.ConeGroupMeasures F C Q I maps

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The fixed cone's group models and compatible Haar measures follow from
Lie integration and exponential Haar measure. Only the original published
inputs are used; arbitrary pure-word sections can be installed afterward. -/
theorem nonempty_measuredCone
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrateQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrateI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := F.N.modelSpace) (G := F.N.carrier))
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : F.N.carrier →* Aˣ)
    (hρ : Function.Injective ρ)
    (hmatch : ∀ v, ρ (F.ExpN (F.N.equiv v)) = algebraExpUnit (j v)) :
    Nonempty (M.MeasuredCone F C) := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨Q, expQ, heQ, π, σ, hπ, hπe, hσ, _, hker, _⟩ :=
    M.exists_cone_group_quotient C F.N F.ExpN F.isExpN haarN existQ haarQ integrateQ
  obtain ⟨I, expI, heI, ι, hi, _, hie, hir⟩ :=
    M.exists_cone_ideal_group C F.N F.ExpN F.isExpN haarN π hker existI haarI integrateI
  let : IsTopologicalGroup I.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, I.modelSpace)) ⊤
  obtain ⟨⟨chartQ, hcQ⟩, hμQ⟩ := (haarQ Q).2 expQ heQ
    (Q.tangent_nilpotent (M.coneQuotient_nilpotent C))
  obtain ⟨⟨chartI, hcI⟩, _⟩ := (haarI I).2 expI heI
    (I.tangent_nilpotent (M.coneIdeal_nilpotent C))
  obtain ⟨⟨chartN, hcN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (LieModule.IsNilpotent.mk _ M.bound_zero))
  have hbijN : Function.Bijective F.ExpN := funext hcN ▸ chartN.bijective
  obtain ⟨μI, hI, hK, hconj, hright⟩ :=
    M.exists_cone_kernel_invariant_haar C I.equiv expI heI (haarI I)
      (finBasis ℝ (M.coneWordIdeal C)) π ι hi hir (F.ExpN ∘ F.N.equiv)
      (hbijN.comp F.N.equiv.bijective).surjective hie j ρ hρ hmatch
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map Q.equiv.toLinearEquiv
  let μQ := Measure.map (expQ ∘ bQ.equivFun.symm) volume
  have hQ : μQ.IsHaarMeasure := hμQ _ bQ
  let maps : M.ConeGroupMaps F C Q I := {
    expQ := expQ, expI := expI, isExpQ := heQ, isExpI := heI
    chartQ := chartQ, chartI := chartI, chartQ_eq := hcQ, chartI_eq := hcI
    quotient := π, quotient_continuous := hπ.continuous
    sectionMap := σ, section_rightInverse := hσ, kernel_eq := hker, quotient_exp := hπe
    inclusion := ι, inclusion_closed := hi, inclusion_exp := hie, inclusion_range := hir }
  exact ⟨{
    Q := Q, I := I, maps := maps
    measures := {
      measureQ := μQ, measureI := μI, haarQ := hQ, haarI := hI
      haarKernel := hK, conjugation_invariant := hconj, kernel_rightInvariant := hright } }⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
