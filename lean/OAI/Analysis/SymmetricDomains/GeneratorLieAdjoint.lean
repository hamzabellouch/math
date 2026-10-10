import Mathlib
import OAI.Analysis.SymmetricDomains.CompleteGeneratorLieAlgebra
import OAI.Analysis.SymmetricDomains.GeneratorAdjointHom

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
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem pushForwardGenerator_lieBracket (q : Biholomorph U U)
    {X Y : Affine n → Affine n} (hX : IsCompleteGenerator U X)
    (hY : IsCompleteGenerator U Y) :
    pushForwardGenerator q (VectorField.lieBracket ℂ X Y) =
      VectorField.lieBracket ℂ (pushForwardGenerator q X) (pushForwardGenerator q Y) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  let b : ℝ → Biholomorph U U := fun t => q*a t*q⁻¹
  have hb : Continuous b := (continuous_const.mul ha).mul continuous_const
  have hb0 : b 0=1 := by simp [b,ha0]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t
    dsimp only [b]
    rw [ham]
    group
  have hgen : infinitesimalGenerator b=pushForwardGenerator q (infinitesimalGenerator a) :=
    infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q
  funext x
  by_cases hx : x∈U
  · let y : U := q.toHomeomorph.symm ⟨x,hx⟩
    have hd1 := pushForwardGenerator_hasDerivAt_zero hU hbd b hb hb0 hbm
      (pushForwardGenerator q Y) ((hY.pushForward hU hbd q).analyticOnNhd hU hbd) x hx
    rw [hgen] at hd1
    have hd2 := ((q.derivativeAt y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
        (hY.analyticOnNhd hU hbd) y.val y.property)
    have heq : (fun t => (q.derivativeAt y) (pushForwardGenerator (a t) Y y.val))=
        (fun t => pushForwardGenerator (b t) (pushForwardGenerator q Y) x) := by
      funext t
      rw [← pushForwardGenerator_mul hU]
      have hg : b t*q=q*a t := by dsimp only [b]; group
      rw [hg,pushForwardGenerator_mul hU]
      exact (pushForwardGenerator_apply q _ ⟨x,hx⟩).symm
    change HasDerivAt (fun t => (q.derivativeAt y) (pushForwardGenerator (a t) Y y.val))
      ((q.derivativeAt y) (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y y.val)) 0 at hd2
    rw [heq] at hd2
    have hd := hd1.unique hd2
    rw [map_neg] at hd
    rw [pushForwardGenerator,dite_eq_left hx]
    exact (neg_injective hd).symm
  · have hqX : pushForwardGenerator q (infinitesimalGenerator a) x=0 := by
      simp only [pushForwardGenerator,dite_eq_right hx]
    have hqY : pushForwardGenerator q Y x=0 := by
      simp only [pushForwardGenerator,dite_eq_right hx]
    rw [pushForwardGenerator,dite_eq_right hx,
      VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ) hqX hqY]

variable (hc : IsConnected U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def generatorLieAdjoint (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ⁅ℝ⁆ completeGeneratorSpace hU hc hbd Γ hhol where
  __ := generatorAdjoint hU hc hbd Γ hhol q
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact pushForwardGenerator_lieBracket hU hbd q X.property Y.property
end Biholomorph
end Release061

end

end OAI
