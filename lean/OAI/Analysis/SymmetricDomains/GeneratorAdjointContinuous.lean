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

namespace Biholomorph

section
open Set Filter Topology Metric
open scoped Classical
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)

def oneParameterGenerator : completeGeneratorSpace hU hc hbd Γ hhol :=
  ⟨infinitesimalGenerator a,⟨a,ha,ha0,ham,rfl⟩⟩
include hU hc hbd Γ hhol ha ha0 ham

theorem generatorAdjoint_slope_tendsto (Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    Tendsto (fun t : ℝ => t⁻¹ • (generatorAdjoint hU hc hbd Γ hhol (a t) Y-
        generatorAdjoint hU hc hbd Γ hhol (a 0) Y)) (𝓝[≠] 0)
      (𝓝 (-⁅oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham,Y⁆)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  have hd : HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y.val x)
      (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y.val x) 0 := by
    by_cases hx : x∈U
    · exact pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y.val
        (Y.property.analyticOnNhd hU hbd) x hx
    · have hbr := VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ)
        (infinitesimalGenerator_of_not_mem a hx) (Y.property.eq_zero_of_not_mem hx)
      simpa only [pushForwardGenerator,dite_eq_right hx,hbr,neg_zero] using
        hasDerivAt_const (0:ℝ) (0 : Affine n)
  apply hd.tendsto_slope.congr'
  filter_upwards [] with t
  change (t-(0:ℝ))⁻¹ • (pushForwardGenerator (a t) Y.val x-pushForwardGenerator (a 0) Y.val x)=
    t⁻¹ • (pushForwardGenerator (a t) Y.val x-pushForwardGenerator (a 0) Y.val x)
  rw [sub_zero]

theorem generatorAdjoint_coordinates_hasDerivAt_zero {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))
    (Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    HasDerivAt (fun t : ℝ => b.equivFun (generatorAdjoint hU hc hbd Γ hhol (a t) Y))
      (b.equivFun (-⁅oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham,Y⁆)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (continuous_equivFun_basis b).continuousAt.tendsto.comp
    (generatorAdjoint_slope_tendsto hU hc hbd Γ hhol a ha ha0 ham Y)
  apply ht.congr'
  filter_upwards [] with t
  simp only [Function.comp_apply,slope_def_module,sub_zero,map_smul,map_sub]

end

open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem generatorAdjoint_continuous (Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    Continuous (fun q : Biholomorph U U => generatorAdjoint hU hc hbd Γ hhol q Y) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun q : Biholomorph U U => (generatorAdjoint hU hc hbd Γ hhol q Y).val x)
  by_cases hx : x∈U
  · let y : Biholomorph U U → U := fun q => q⁻¹.toHomeomorph ⟨x,hx⟩
    have hy : Continuous y := (continuous_evaluation ⟨x,hx⟩).comp continuous_inv
    apply continuous_iff_continuousAt.mpr
    intro q
    have hD := (ambientAut_derivative_joint_continuousAt hU (y q).property).comp
      (f := fun q : Biholomorph U U => (q,(y q).val))
      (continuous_id.prodMk (continuous_subtype_val.comp hy)).continuousAt
    have hY := ((Y.property.analyticOnNhd hU hbd) (y q).val (y q).property).continuousAt.comp
      (f := fun q => (y q).val) (x := q) (continuous_subtype_val.comp hy).continuousAt
    have hh := hD.clm_apply hY
    change ContinuousAt (fun q : Biholomorph U U => pushForwardGenerator q Y.val x) q
    have heq : (fun q : Biholomorph U U => pushForwardGenerator q Y.val x)=
        (fun q => fderiv ℂ q.ambientAut (y q).val (Y.val (y q).val)) := by
      funext q
      rw [pushForwardGenerator,dite_eq_left hx]
      rfl
    rw [heq]
    exact hh
  · have heq : (fun q : Biholomorph U U => (generatorAdjoint hU hc hbd Γ hhol q Y).val x) =
        fun _ => 0 := by
      funext q
      exact (generatorAdjoint hU hc hbd Γ hhol q Y).property.eq_zero_of_not_mem hx
    rw [heq]
    exact continuous_const
end Biholomorph
end Release061

end

end OAI
