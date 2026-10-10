import Mathlib
import OAI.Analysis.SymmetricDomains.EulerSpectrum
import OAI.Analysis.SymmetricDomains.ModelComplexField
import OAI.Analysis.SymmetricDomains.Geometry2

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
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph
open Set Filter Topology
open scoped TensorProduct
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem modelComplexField_ofReal (e : Biholomorph U D)
    (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    modelComplexField hU hc hbd Γ hhol e (Complexification.ofReal X)=coordinateField e X.val := by
  simp only [modelComplexField, LinearMap.comp_apply, Complexification.ofReal_apply,
    complexGeneratorField_tmul, one_smul]
  rfl

 theorem exists_actual_weightedLieModel {r k : ℕ} (D : Set (Affine r × Affine k))
    (hDo : IsOpen D)
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U)
    (a : Fin k → ℝ) (ha : (0,fun i => Complex.I*(a i : ℂ))∈D) :
    ∃ M : WeightedLieModel r k (completeGeneratorSpace hU hc hbd Γ hhol),
      M.normal=a ∧ M.field=modelComplexField hU hc hbd Γ hhol e.symm := by
  let S := (affineProductCoordinates r k) '' D
  have hS : IsOpen S := (affineProductCoordinates r k).isOpenMap _ hDo
  have hpa : Complex.I • flatNormalVector r k a∈S := by
    have he : Complex.I • flatNormalVector r k a=
        affineProductCoordinates r k (0,fun i => Complex.I*(a i : ℂ)) := by
      rw [flatNormalVector,←map_smul]
      congr 1
      ext i <;> simp
    rw [he]
    exact ⟨_,ha,rfl⟩
  let p : S := ⟨_,hpa⟩
  obtain ⟨E,hE⟩ := exists_actual_model_euler D hd hU hc hbd Γ hhol e
  obtain ⟨H,hH⟩ := exists_actual_model_rotation D hr hU hc hbd Γ hhol e
  obtain ⟨b,hb,hb0,hbm,hbe,T,hT,hnil⟩ := model_normal_translation_ad_nilpotent D htr hd hU hc hbd Γ hhol e a
  have hTf : coordinateField e.symm T.val=S.indicator (fun _ => flatNormalVector r k a) := by
    rw [hT,funext hbe]
    exact transported_translation_generator_in_model hU hbd e _ _
  let F := modelComplexField hU hc hbd Γ hhol e.symm
  have hF (X : completeGeneratorSpace hU hc hbd Γ hhol) :
      F (Complexification.ofReal X)=coordinateField e.symm X.val :=
    modelComplexField_ofReal hU hc hbd Γ hhol e.symm X
  refine ⟨{
    field := F
    normal := a
    euler := E
    translation := T
    rotation := H
    analytic := fun X => modelComplexField_analytic hU hc hbd Γ hhol hS e.symm X _ hpa
    jet_injective := fun X hz => modelComplexField_secondJet_injective hU hc hbd Γ hhol hS e.symm X p hz
    lie := modelComplexField_lie hU hc hbd Γ hhol hS e.symm
    euler_germ := ?_
    translation_germ := ?_
    rotation_germ := ?_
    nilpotent := hnil
    isotropy_real := ?_
  },rfl,rfl⟩
  · rw [hF,hE]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · rw [hF,hTf]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · rw [hF,hH]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · intro X Y hx hy hrel
    simp only [hF] at hx hy hrel
    apply Subtype.ext
    exact model_isotropy_totally_real hU hc hbd hS e.symm Γ hhol X.property Y.property p hx hy hrel

end Release061.Biholomorph

end

end OAI
