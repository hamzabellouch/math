import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalFiniteEndingData
import OAI.Analysis.Conductivity.Flux.PhysicalSplicedGreen
import OAI.Analysis.Conductivity.Variational.CentralCorrectedRepresentative
import OAI.Analysis.Conductivity.Variational.PhysicalEndOpen
import OAI.Analysis.Conductivity.Geometry.PhysicalRegionGluing

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
local instance physicalBlockRepresentativeMeasurableSpace : MeasurableSpace Mat3 := inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance physicalBlockRepresentativeBorelSpace : BorelSpace Mat3 := inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def cartesianTensor
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (y : Coord3) : Symmetric3 :=
  ⟨variableBlockTensor z.flatTensor z.compression y,
    (variableBlockTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne).2.2.1 y⟩

lemma cartesianTensor_measurable
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    Measurable (z.cartesianTensor hs) := by
  change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) (z.cartesianTensor hs)
  rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)]
  exact ((variableBlockTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne).1).subtype_mk

theorem corrected_pair_representative
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (w : Fin 2 → H1)
    (hwc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (physicalBlockRegion \ regularRegion v (z.cartesianTensor hs) physicalBlockRegion)=0 := by
  obtain ⟨u,hu,he,hr⟩ := z.central_representative hwc
  let O : Option (Fin 3) → Set Coord3 := fun i => i.elim centralStrict physicalEndOpen
  let g : Option (Fin 3) → Coord3 → Fin 2 → ℝ := fun i => i.elim u z.endRepresentative
  have hO : ∀ i,IsOpen (O i) := by
    intro i
    cases i with
    | none => exact centralStrict_open
    | some i => exact physicalEndOpen_open i
  have hOU : ∀ i,O i⊆physicalBlockRegion := by
    intro i
    cases i with
    | none => exact fun _ hy => Or.inl (centralStrict_subset hy)
    | some i => exact (physicalEndOpen_subset i).trans (physicalEndRegion_mem_block i)
  have hc : ∀ᵐ y : Coord3,y∈physicalBlockRegion → y∈⋃ i,O i := by
    filter_upwards [centralStrict_conull,ae_all_iff.mpr physicalEndOpen_conull] with y hcc hce hy
    rcases hy with hc|he
    · exact mem_iUnion.mpr ⟨none,hcc hc⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp he
      exact mem_iUnion.mpr ⟨some i,hce i hi⟩
  have hES (i : Fin 3) (y : Coord3) : (variableEndTensor z.flatTensor z.compression i y).IsSymm :=
    (variableEndTensor_properties z.flatTensor z.compression (z.flatTensor_properties hs) z.compression_ne i).2.1 y
  have hreg : ∀ i,∀ᵐ y : Coord3,y∈O i → y∈regularRegion (g i) (z.cartesianTensor hs) (O i) := by
    intro i
    cases i with
    | none =>
      filter_upwards [hr] with y hy hyO
      apply mem_regularRegion_congr_nhds (hy hyO) Filter.EventuallyEq.rfl ?_ centralStrict_open hyO
      filter_upwards [centralStrict_open.mem_nhds hyO] with x hx
      exact Subtype.ext (variableBlockTensor_centralStrict z.flatTensor z.compression hx)
    | some i =>
      filter_upwards [z.endRepresentative_regular hs hES i] with y hy hyO
      apply mem_regularRegion_congr_nhds (hy (physicalEndOpen_subset i hyO)) Filter.EventuallyEq.rfl ?_
        (physicalEndOpen_open i) hyO
      filter_upwards [(physicalEndOpen_open i).mem_nhds hyO] with x hx
      exact Subtype.ext (variableBlockTensor_local z.flatTensor z.compression i (physicalEndOpen_subset i hx))
  have he' : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i := by
    intro i
    apply (ae_restrict_iff' (hO i).measurableSet).mpr
    cases i with
    | none =>
      filter_upwards [he] with y hy hyO
      exact (hy hyO).symm
    | some i =>
      have hv (j : Fin 2) := z.endRepresentative_value hs i j
      have hw (j : Fin 2) := (hwe j i).value_cartesian (fun _ => physicalEndRegion_subset_ball i)
      filter_upwards [ae_all_iff.mpr hv,ae_all_iff.mpr hw] with y hv hw hyO
      funext j
      exact (hw j (physicalEndOpen_subset i hyO)).trans (hv j (physicalEndOpen_subset i hyO))
  exact physical_region_glue O hO physicalBlockRegion_compact.measurableSet hOU
    (fun _ => physicalBlockRegion_subset_ball) hc w g (z.cartesianTensor hs) hreg he'

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
