import Mathlib
import OAI.Analysis.SymmetricDomains.GeneratorAdjointContinuous

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

section
open Set Filter Topology Matrix

theorem hasDerivAt_matrix_det_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → Matrix ι ι ℝ} {A : Matrix ι ι ℝ} {s : ℝ}
    (hf : HasDerivAt f A s) (hfs : f s=1) :
    HasDerivAt (fun t => (f t).det) A.trace s := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  have hd := (D.hasFDerivAt (f s)).comp_hasDerivAt s hf
  have hlin : D.linearDeriv (f s) A=A.trace := by
    have he := D.linearDeriv_apply (f s) A
    rw [he,hfs]
    apply Finset.sum_congr rfl
    intro i hi
    change (Matrix.updateRow (1 : Matrix ι ι ℝ) i (A i)).det=A i i
    have heq : (∑ k : ι, (A i k) • (1 : Matrix ι ι ℝ) k)=A i := by
      funext j
      simp [Matrix.one_apply]
    rw [← heq,Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one,heq]
  rw [hlin] at hd
  exact hd
end

open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))

def generatorAdjointMatrix (q : Biholomorph U U) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b b (generatorAdjoint hU hc hbd Γ hhol q).toLinearMap

 theorem generatorAdjointMatrix_one : generatorAdjointMatrix hU hc hbd Γ hhol b 1=1 := by
  have h := (generatorAdjointHom hU hc hbd Γ hhol).map_one
  change generatorAdjoint hU hc hbd Γ hhol 1=1 at h
  unfold generatorAdjointMatrix
  rw [h]
  exact LinearMap.toMatrix_one b

 theorem generatorAdjointMatrix_mul (q r : Biholomorph U U) :
    generatorAdjointMatrix hU hc hbd Γ hhol b (q*r)=
      generatorAdjointMatrix hU hc hbd Γ hhol b q * generatorAdjointMatrix hU hc hbd Γ hhol b r := by
  have h := (generatorAdjointHom hU hc hbd Γ hhol).map_mul q r
  change generatorAdjoint hU hc hbd Γ hhol (q*r)=
    generatorAdjoint hU hc hbd Γ hhol q * generatorAdjoint hU hc hbd Γ hhol r at h
  unfold generatorAdjointMatrix
  rw [h]
  exact LinearMap.toMatrix_mul b _ _

 theorem generatorAdjointMatrix_continuous : Continuous (generatorAdjointMatrix hU hc hbd Γ hhol b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [generatorAdjointMatrix,LinearMap.toMatrix_apply]
  exact (continuous_apply i).comp ((continuous_equivFun_basis b).comp
    (generatorAdjoint_continuous hU hc hbd Γ hhol (b j)))

def generatorDeterminant : Biholomorph U U →* ℝ where
  toFun q := (generatorAdjointMatrix hU hc hbd Γ hhol b q).det
  map_one' := by rw [generatorAdjointMatrix_one,Matrix.det_one]
  map_mul' q r := by rw [generatorAdjointMatrix_mul,Matrix.det_mul]

 theorem generatorDeterminant_continuous : Continuous (generatorDeterminant hU hc hbd Γ hhol b) :=
  (generatorAdjointMatrix_continuous hU hc hbd Γ hhol b).matrix_det

 theorem generatorDeterminant_ne_zero (q : Biholomorph U U) :
    generatorDeterminant hU hc hbd Γ hhol b q≠0 := by
  intro he
  have h := (generatorDeterminant hU hc hbd Γ hhol b).map_mul q q⁻¹
  rw [mul_inv_cancel,map_one,he,zero_mul] at h
  exact one_ne_zero h

variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)

 theorem generatorAdjointMatrix_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => generatorAdjointMatrix hU hc hbd Γ hhol b (a t))
      (-LinearMap.toMatrix b b (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
        (oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham))) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := hasDerivAt_pi.mp
    (generatorAdjoint_coordinates_hasDerivAt_zero hU hc hbd Γ hhol a ha ha0 ham b (b j)) i
  simpa only [generatorAdjointMatrix,Matrix.neg_apply,LinearMap.toMatrix_apply,
    map_neg,Pi.neg_apply,Module.Basis.equivFun_apply,LieAlgebra.ad_apply,LinearEquiv.coe_coe] using h

theorem generatorDeterminant_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => generatorDeterminant hU hc hbd Γ hhol b (a t))
      (-LinearMap.trace ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
        (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
          (oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham))) 0 := by
  have h := hasDerivAt_matrix_det_one
    (generatorAdjointMatrix_hasDerivAt_zero hU hc hbd Γ hhol b a ha ha0 ham)
    (by rw [ha0,generatorAdjointMatrix_one])
  simpa only [generatorDeterminant,MonoidHom.coe_mk,OneHom.coe_mk,Matrix.trace_neg,
    LinearMap.trace_eq_matrix_trace ℝ b] using h

include ham in
 theorem generatorDeterminant_flow_pos (t : ℝ) :
    0<generatorDeterminant hU hc hbd Γ hhol b (a t) := by
  have h : t=t/2+t/2 := by ring
  rw [h,ham,map_mul]
  exact mul_self_pos.mpr (generatorDeterminant_ne_zero hU hc hbd Γ hhol b (a (t/2)))
end Biholomorph
end Release061

end

end OAI
