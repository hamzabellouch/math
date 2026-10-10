import Mathlib
import OAI.Geometry.Borsuk.Support.ActiveChambers
import OAI.Geometry.Borsuk.Support.NegativeFibre

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
open Set
section PurityChart
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def purityChart (f : E → ι → ℝ) (I : Finset ι) (w c : E) : Set M :=
  {A | IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
    lineRepresentative w A ∈ commonPositiveCone f I ∧
    lineRepresentative w A ∈ interior (signChamber (activeVectors f I) c)}

omit [Nonempty ν] in
lemma Admissible.purityChart_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : E) {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen (A ⁻¹' purityChart f I w c) := by
  have hop : Continuous (fun x => op (A x)⁺ w) :=
    (((op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (matrix_posPart_continuousOn.comp_continuous hA hSA)).clm_apply continuous_const
  have hopen : IsOpen {x | op (A x)⁺ w ≠ 0} := (isClosed_eq hop continuous_const).isOpen_compl
  have hrep := lineRepresentative_continuousOn A hA hSA w
  have hpre : IsOpen ({x | op (A x)⁺ w ≠ 0} ∩
      (fun x => lineRepresentative w (A x)) ⁻¹'
      (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) :=
    hrep.isOpen_inter_preimage hopen ((hf.commonPositiveCone_isOpen I).inter isOpen_interior)
  have hn : IsOpen {x | 0 < Matrix.trace (A x)⁻} := isOpen_lt continuous_const
    (matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA))
  have he : A ⁻¹' purityChart f I w c =
      ({x | IsUnit (A x) ∧ HasPositiveLine (A x)} ∩ {x | 0 < Matrix.trace (A x)⁻}) ∩
        ({x | op (A x)⁺ w ≠ 0} ∩ (fun x => lineRepresentative w (A x)) ⁻¹'
          (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) := by
    ext x
    simp only [purityChart,mem_preimage,mem_ofPred_eq,mem_inter_iff]
    tauto
  rw [he]
  exact ((positive_line_isOpen A hA hSA).inter hn).inter hpre

omit [Fintype ι] in
omit [Nonempty ν] in
lemma purityChart_unit {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hA : A ∈ purityChart f I w c) : ‖lineRepresentative w A‖ = 1 :=
  lineRepresentative_norm hA.2.2.1

omit [Fintype ι] in
lemma purityChart_fibre {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hA : A ∈ purityChart f I w c) : negativeFibre A ∈ matrixFibre (lineRepresentative w A) :=
  negativeFibre_mem hA.2.1 hA.2.2.1 hA.2.2.2.1

omit [Fintype ι] in
lemma purityChart_fibre_unit {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
    IsUnit (rankOne (lineRepresentative w A) + negativeFibre A) := by
  have hf := purityChart_fibre hA
  apply fibre_unit_of_split_unit hf.1 hf.2.2 (hasPositiveLine_trace_pos hA.2.1) hA.2.2.2.1
  rw [← negativeFibre_splitting hSA hA.2.1 hA.2.2.1 hA.2.2.2.1]
  exact hA.1

end PurityChart
end BorsukNine

end OAI
