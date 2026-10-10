import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialRelationDependentPartials

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Algebra KaehlerDifferential Module
open scoped TensorProduct

def differentialSubfield {R K : Type*} [Field R] [Field K] [Algebra R K]
    (M : Submodule K Ω[K⁄R]) : IntermediateField R K where
  carrier := {x | D R K x ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro x y hx hy; simpa only [mem_ofPred_eq, map_add] using M.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    change D R K (x*y) ∈ M
    rw [Derivation.leibniz]
    exact M.add_mem (M.smul_mem x hy) (M.smul_mem y hx)
  inv_mem' := by
    intro x hx
    change D R K x⁻¹ ∈ M
    rw [Derivation.leibniz_inv]
    exact M.smul_mem _ hx
  algebraMap_mem' := by intro r; simp

theorem differential_mem_span_adjoin {R K κ : Type*}
    [Field R] [Field K] [Algebra R K] (q : κ → K)
    {y : K} (hy : y ∈ IntermediateField.adjoin R (range q)) :
    D R K y ∈ Submodule.span K (range (fun j => D R K (q j))) := by
  have hle : IntermediateField.adjoin R (range q) ≤
      differentialSubfield (Submodule.span K (range (fun j => D R K (q j)))) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span (mem_range_self j)
  exact hle hy

theorem differential_mem_span_transcendenceBasis
    {R L K ι : Type*} [Field R] [CharZero R] [Field L] [Field K]
    [Algebra R L] [Algebra R K] [Algebra L K] [IsScalarTower R L K]
    (x : ι → L) (hx : IsTranscendenceBasis R x) (y : L) :
    D R K (algebraMap L K y) ∈
      Submodule.span K (range (fun i => D R K (algebraMap L K (x i)))) := by
  let M := Submodule.span K (range (fun i => D R K (algebraMap L K (x i))))
  change _ ∈ M
  rw [← KaehlerDifferential.map_D (R := R) (S := R) (A := L) (B := K)]
  have hmem : D R L y ∈ Submodule.span L (range (transcendenceDifferentialBasis x hx)) := by
    rw [(transcendenceDifferentialBasis x hx).span_eq]
    trivial
  generalize D R L y = z at hmem ⊢
  induction hmem using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i,rfl⟩ := hz
    simp only [transcendenceDifferentialBasis_apply, KaehlerDifferential.map_D]
    exact Submodule.subset_span (mem_range_self i)
  | zero => exact by simp
  | add z w _ _ hz hw => simpa only [map_add] using M.add_mem hz hw
  | smul a z _ hz =>
    rw [map_smul]
    exact (M.restrictScalars L).smul_mem a hz

end Release061

end

end OAI
