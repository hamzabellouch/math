import Mathlib
import OAI.Analysis.SymmetricDomains.PositiveReal
import OAI.Analysis.SymmetricDomains.PositiveVertexJets
import OAI.Analysis.SymmetricDomains.Geometry3
import OAI.Analysis.SymmetricDomains.CompleteGeneratorTraceAd
import OAI.Analysis.SymmetricDomains.ModelIsotropyCentralShift

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

section
open Set
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

theorem coordinateField_scalar_derivative (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (c : ℂ) (hx : coordinateField e X p.val=0)
    (hd : fderiv ℂ (coordinateField e X) p.val=c • (1 : Affine m →L[ℂ] Affine m)) :
    fderiv ℂ X (e.toHomeomorph.symm p).val=c • (1 : Affine n →L[ℂ] Affine n) := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  rw [coordinateField_fderiv_of_zero hU hD e hX p hx0] at hd
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  apply ContinuousLinearMap.ext
  intro v
  have hh := congrArg (fun L : Affine m →L[ℂ] Affine m => L (A v)) hd
  have hi : e.symm.mapDerivative p (A v)=v := by
    have he := congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
      (mapDerivative_symm_comp hU hD e (e.toHomeomorph.symm p))
    simpa only [A,mapDerivativeEquiv_apply,e.toHomeomorph.apply_symm_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using he
  change A (fderiv ℂ X (e.toHomeomorph.symm p).val (e.symm.mapDerivative p (A v)))=c • A v at hh
  rw [hi,←map_smul] at hh
  exact A.injective hh

theorem model_negative_isotropy_of_scalar_generator
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
    {X : Affine n → Affine n} (hX : IsCompleteGenerator U X) (p : D)
    (hx : coordinateField e X p.val=0)
    (hd : fderiv ℂ (coordinateField e X) p.val=(2*Complex.I) • (1 : Affine m →L[ℂ] Affine m)) :
    ∃ a : Biholomorph U U, a.toHomeomorph (e.toHomeomorph.symm p)=e.toHomeomorph.symm p ∧
      a.derivativeAt (e.toHomeomorph.symm p)= -1 := by
  apply negative_isotropy_of_scalar_generator hU hbd hX (e.toHomeomorph.symm p)
  · exact (coordinateField_value_zero_iff hU hD e X p).mp hx
  · exact coordinateField_scalar_derivative hU hD e (hX.analyticOnNhd hU hbd) p (2*Complex.I) hx hd
end

open Set Filter Topology
open scoped TensorProduct

theorem flatTangentialInfinitesimal_euler (r k : ℕ) :
    flatTangentialInfinitesimal r k=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-(2 : ℂ) • flatWeightedEuler r k) := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  change flatTangentialInfinitesimal r k (modelBasis r k j)=
    Complex.I • ((2 : ℂ) • modelBasis r k j-(2 : ℂ) • flatWeightedEuler r k (modelBasis r k j))
  rw [flatTangentialInfinitesimal_basis,flatWeightedEuler_basis]
  cases j <;> simp only [modelRotationWeight,modelEulerWeight] <;> module

variable {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

include hU hc hbd Γ hhol in

theorem model_axis_negative_isotropy {r k : ℕ} (D : Set (Affine r × Affine k))
    (hDo : IsOpen D)
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U)
    (p : (affineProductCoordinates r k) '' D) (a : Fin k → ℝ)
    (hp : p.val=Complex.I • flatNormalVector r k a) :
    ∃ b : Biholomorph U U, b.toHomeomorph (e.toHomeomorph p)=e.toHomeomorph p ∧
      b.derivativeAt (e.toHomeomorph p)= -1 := by
  let S := (affineProductCoordinates r k) '' D
  have hS : IsOpen S := (affineProductCoordinates r k).isOpenMap _ hDo
  have hpa : affineProductCoordinates r k (0,fun i => Complex.I*(a i : ℂ))=p.val := by
    rw [hp,flatNormalVector,←map_smul]
    congr 1
    ext i <;> simp
  have ha : (0,fun i => Complex.I*(a i : ℂ))∈D := by
    obtain ⟨q,hq,hqp⟩ := p.property
    have hqeq := (affineProductCoordinates r k).injective (hqp.trans hpa.symm)
    simpa only [hqeq] using hq
  let G := completeGeneratorSpace hU hc hbd Γ hhol
  let _ : FiniteDimensional ℝ G := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  obtain ⟨M,hnormal,hfield⟩ := exists_actual_weightedLieModel hU hc hbd Γ hhol D hDo htr hd hr e a ha
  have hpoint : M.point=p.val := by rw [WeightedLieModel.point,hnormal,hp]
  have hF (X : G) : M.field (Complexification.ofReal X)=coordinateField e.symm X.val := by
    rw [hfield,modelComplexField_ofReal]
  obtain ⟨V,hV,hTV⟩ := M.exists_positive_real
    (completeGenerator_trace_ad_eq_zero hU hc hbd Γ hhol M.euler)
  let W : G := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
  let Q : G := M.translation-V+M.rotation
  obtain ⟨hWp,hVp,hVd⟩ := M.positive_vertex_jets V hV hTV
  change M.field (Complexification.ofReal W) M.point=0 at hWp
  change M.firstJet (Complexification.ofReal V)=
    Complex.I • (M.firstJet (Complexification.ofReal W)-(2 : ℂ) • flatWeightedEuler r k) at hVd
  have hQp : M.field (Complexification.ofReal Q) M.point=0 := by
    simp only [Q,map_add,map_sub,Pi.add_apply,Pi.sub_apply,M.field_translation_value,hVp,
      M.field_rotation_value,sub_self,add_zero]
  have hQd : M.firstJet (Complexification.ofReal Q)=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-M.firstJet (Complexification.ofReal W)) := by
    simp only [Q,map_add,map_sub,M.firstJet_translation,M.firstJet_rotation,hVd]
    rw [flatTangentialInfinitesimal_euler]
    module
  have hWzero : W=0 := by
    have hx := hWp
    have hy := hQp
    have hrel := hQd
    change fderiv ℂ (M.field (Complexification.ofReal Q)) M.point=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-
        fderiv ℂ (M.field (Complexification.ofReal W)) M.point) at hrel
    simp only [hF,hpoint] at hx hy hrel
    apply Subtype.ext
    exact model_isotropy_central_shift_zero hU hc hbd hS e.symm Γ hhol W.property Q.property p 2 hx hy
      (by simpa only [Complex.ofReal_ofNat] using hrel)
  have hQscalar : M.firstJet (Complexification.ofReal Q)=
      (2*Complex.I) • (1 : Affine (r+k) →L[ℂ] Affine (r+k)) := by
    rw [hQd,hWzero,map_zero,map_zero,sub_zero,smul_smul]
    congr 1
    ring
  change fderiv ℂ (M.field (Complexification.ofReal Q)) M.point=_ at hQscalar
  simp only [hF,hpoint] at hQp hQscalar
  exact model_negative_isotropy_of_scalar_generator hU hbd hS e.symm Q.property p hQp hQscalar

end Release061.Biholomorph

end

end OAI
