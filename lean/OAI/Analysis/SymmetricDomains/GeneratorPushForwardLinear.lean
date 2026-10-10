import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteDimensionalCompleteGenerator

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
open Set Filter Topology Metric
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def pushForwardGenerator (q : Biholomorph U U) (X : Affine n → Affine n)
    (x : Affine n) : Affine n :=
  if hx : x∈U then q.derivativeAt (q.toHomeomorph.symm ⟨x,hx⟩)
    (X (q.toHomeomorph.symm ⟨x,hx⟩).val) else 0

@[simp] theorem pushForwardGenerator_apply (q : Biholomorph U U) (X : Affine n → Affine n) (x : U) :
    pushForwardGenerator q X x.val=q.derivativeAt (q.toHomeomorph.symm x) (X (q.toHomeomorph.symm x).val) := by
  simp only [pushForwardGenerator,dite_eq_left x.property]

theorem infinitesimalGenerator_conjugate (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (q : Biholomorph U U) :
    infinitesimalGenerator (fun t => q*a t*q⁻¹)=pushForwardGenerator q (infinitesimalGenerator a) := by
  funext x
  by_cases hx : x∈U
  · let y : U := q.toHomeomorph.symm ⟨x,hx⟩
    have hy : (a 0).ambientAut y.val=y.val := by rw [ha0,ambientAut_apply,one_apply]
    have hq : HasFDerivAt q.ambientAut ((q.derivativeAt y).restrictScalars ℝ) ((a 0).ambientAut y.val) := by
      rw [hy]
      exact ((q.ambientAut_analytic hU y.val y.property).differentiableAt.hasFDerivAt).restrictScalars ℝ
    have hcomp := hq.comp_hasDerivAt 0 (infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham y.val)
    have heq : (fun t => q.ambientAut ((a t).ambientAut y.val))=
        (fun t => (q*a t*q⁻¹).ambientAut x) := by
      funext t
      rw [ambientAut_apply (q*a t*q⁻¹) ⟨x,hx⟩,mul_apply,mul_apply,
        ambientAut_apply,ambientAut_apply]
      rfl
    have hcomp' : HasDerivAt (fun t => (q*a t*q⁻¹).ambientAut x)
        ((q.derivativeAt y) (infinitesimalGenerator a y.val)) 0 := by
      change HasDerivAt (fun t => q.ambientAut ((a t).ambientAut y.val))
        ((q.derivativeAt y) (infinitesimalGenerator a y.val)) 0 at hcomp
      rwa [heq] at hcomp
    change deriv (fun t => (q*a t*q⁻¹).ambientAut x) 0=pushForwardGenerator q (infinitesimalGenerator a) x
    rw [hcomp'.deriv,pushForwardGenerator,dite_eq_left hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,pushForwardGenerator,dite_eq_right hx]

theorem IsCompleteGenerator.pushForward (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (q : Biholomorph U U) :
    IsCompleteGenerator U (pushForwardGenerator q X) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  refine ⟨fun t => q*a t*q⁻¹,continuous_const.mul ha |>.mul continuous_const,by simp [ha0],?_,
    infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q⟩
  intro s t
  dsimp only
  rw [ham]
  group

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem completeGeneratorSpace_isClosed :
    IsClosed (completeGeneratorSpace hU hc hbd Γ hhol : Set (Affine n → Affine n)) := by
  have := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  exact Submodule.closed_of_finiteDimensional _

include hU hc hbd Γ hhol in

theorem isCompleteGenerator_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    (X : ι → Affine n → Affine n) (Y : Affine n → Affine n)
    (hX : ∀ᶠ i in l, IsCompleteGenerator U (X i))
    (ht : ∀ x, Tendsto (fun i => X i x) l (𝓝 (Y x))) : IsCompleteGenerator U Y := by
  exact (completeGeneratorSpace_isClosed hU hc hbd Γ hhol).mem_of_tendsto
    (tendsto_pi_nhds.mpr ht) hX

def generatorPushForwardLinear (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol →ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol where
  toFun X := ⟨pushForwardGenerator q X.val,X.property.pushForward hU hbd q⟩
  map_add' X Y := by
    apply Subtype.ext
    funext x
    by_cases hx : x∈U
    · simp only [pushForwardGenerator,dite_eq_left hx,Submodule.coe_add,Pi.add_apply,map_add]
    · simp only [pushForwardGenerator,dite_eq_right hx,Submodule.coe_add,Pi.add_apply,add_zero]
  map_smul' c X := by
    apply Subtype.ext
    funext x
    by_cases hx : x∈U
    · simp only [pushForwardGenerator,dite_eq_left hx,Submodule.coe_smul,Pi.smul_apply,ContinuousLinearMap.map_smul_of_tower,RingHom.id_apply]
    · simp only [pushForwardGenerator,dite_eq_right hx,Submodule.coe_smul,Pi.smul_apply,smul_zero]

end Biholomorph
end Release061

end

end OAI
