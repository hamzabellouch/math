import OAI.NumberTheory.DukePrimeDegree.Geometry.DiracFiberGraph

namespace OAI

/-! # Remove the independent neutral coordinate from a full-measure graph -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U V : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]

theorem independent_graph_slice
    (ρ : Measure (Z × U)) [SFinite ρ] (η : Measure V) [SFinite η] [NeZero η]
    (E : Set ((Z × U) × V)) (hE : MeasurableSet E)
    (hfull : ∀ᵐ x ∂ρ.prod η, x ∈ E)
    (hunique : ∀ x ∈ E, ∀ y ∈ E,
      x.1.1=y.1.1 → x.2=y.2 → x.1.2=y.1.2) :
    ∃ F : Set (Z × U), MeasurableSet F ∧ (∀ᵐ z ∂ρ, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂ρ.prod η, z.1 ∈ F) := by
  have hv : ∀ᵐ v ∂η, ∀ᵐ z ∂ρ, (z,v) ∈ E :=
    (Measure.ae_ae_comm (p := fun z v => (z,v) ∈ E) hE).mp
      (Measure.ae_ae_of_ae_prod hfull)
  obtain ⟨v,hv⟩ := hv.exists
  let F : Set (Z × U) := (fun z => (z,v)) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage measurable_prodMk_right
  refine ⟨F,hF,hv,?_,?_⟩
  · intro x hx y hy hxy
    exact hunique (x,v) hx (y,v) hy hxy rfl
  · apply (Measure.ae_prod_iff_ae_ae (hF.preimage measurable_fst)).mpr
    filter_upwards [hv] with z hz
    exact Filter.Eventually.of_forall fun _ => hz

theorem independent_graph_of_fiber_map
    {S W : Type*} [MeasurableSpace S] [MeasurableSpace W] [StandardBorelSpace W]
    (ρ : Measure (Z × U)) [SFinite ρ] (η : Measure V) [SFinite η] [NeZero η]
    (θ : Measure (S × W)) (κ : Kernel S W) [IsFiniteKernel κ]
    (hatom : ∀ᵐ z ∂θ, κ z.1=Measure.dirac z.2)
    (Φ : (Z × U) × V → S × W) (hΦ : Measurable Φ)
    (hac : (ρ.prod η).map Φ ≪ θ)
    (hbase : ∀ x y, x.1.1=y.1.1 → x.2=y.2 → (Φ x).1=(Φ y).1)
    (hinj : ∀ x y, x.1.1=y.1.1 → x.2=y.2 →
      (Φ x).2=(Φ y).2 → x.1.2=y.1.2) :
    ∃ F : Set (Z × U), MeasurableSet F ∧ (∀ᵐ z ∂ρ, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂ρ.prod η, z.1 ∈ F) := by
  let E := Φ ⁻¹' kernelDiracGraph κ
  have hE : MeasurableSet E := (measurableSet_kernelDiracGraph κ).preimage hΦ
  have hfull : ∀ᵐ z ∂ρ.prod η, z ∈ E :=
    ae_of_ae_map hΦ.aemeasurable (hac.ae_le hatom)
  apply independent_graph_slice ρ η E hE hfull
  intro x hx y hy hN hv
  apply hinj x y hN hv
  exact kernelDiracGraph_fiber_unique κ hx hy (hbase x y hN hv)

end DukePrimeDegree

end

end OAI
