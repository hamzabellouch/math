import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingGroupCenter
import OAI.NumberTheory.DukePrimeDegree.Geometry.ProportionalWindowMeasures
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixAmbientGood

namespace OAI

/-! # Large-window conditionals determine the proportional class of an actual leaf -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {F : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P F}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_basedGroup_proportional_window
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (D : RootPrefixBox C c hP hf g) (hAD : A.time ⊆ D.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (η : X n → Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)))
    (hD : ∀ᵐ z ∂D.coordinateMeasure μ,
      let V := c.remainingGroupCenter hP hf z.2 '' D.time
      c.remainingGroupLeafMeasure hP hf
        (c.centeredRemainingMeasure hP hf (D.conditionalKernel μ z.1) z.2) =
        (anchorNormalize (η (C.timeParam c hP hf g z)) V).restrict V) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z.1 ∈ D.transverse →
      ∃ a : ℝ≥0∞,
        (c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z)).restrict
          (c.remainingGroupCenter hP hf z.2 '' D.time) =
        a • (η (C.timeParam c hP hf g z)).restrict
          (c.remainingGroupCenter hP hf z.2 '' D.time) := by
  have H := A.ae_coordinate_of_ambient μ (D.ae_ambient_forall_coordinates μ hD)
  have HR := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_leafMeasure_restrict R hAR μ hfree D hAD)
  filter_upwards [H,HR,A.coordinateMeasure_ae_domain μ] with z hz hr hAz
  intro hsD
  have hDz : z ∈ D.domain := ⟨hsD,hAD hAz.2⟩
  have hk := hz z hDz rfl
  let E := (c.remainingGroupCenter hP hf z.2).toMeasurableEquiv
  let ν := A.leafMeasure R μ z.1
  let κ := D.conditionalKernel μ z.1
  let a := (c.centeredRemainingMeasure hP hf ν z.2 (c.cube 1))⁻¹
  let b := (κ A.time)⁻¹
  have hν : ν.restrict D.time = b • κ.restrict D.time := by
    simpa only [anchorNormalize,Measure.restrict_smul] using (hr hsD).2
  have hκ : κ.map E =
      (anchorNormalize (η (C.timeParam c hP hf g z)) (E '' D.time)).restrict (E '' D.time) := by
    rw [show κ.map E = c.remainingGroupLeafMeasure hP hf
      (c.centeredRemainingMeasure hP hf κ z.2) from
        c.remainingGroupCenter_map hP hf κ z.2]
    exact hk
  have hb : c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z) = a • ν.map E :=
    c.basedRemainingGroupMeasure_eq_smul_center hP hf ν z.2
  refine ⟨a*b*((η (C.timeParam c hP hf g z)) (E '' D.time))⁻¹,?_⟩
  rw [hb]
  exact map_restrict_proportional_of_normalized E ν κ (η (C.timeParam c hP hf g z))
    D.time D.time_open.measurableSet a b hν hκ

end RootPrefixBox
end DukePrimeDegree

end

end OAI
