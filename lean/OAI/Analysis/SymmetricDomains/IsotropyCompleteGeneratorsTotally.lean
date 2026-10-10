import Mathlib
import OAI.Analysis.SymmetricDomains.ZeroISmul

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
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
include hU hc hbd
 theorem IsCompleteGenerator.eq_zero_of_zero_jet {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (p : U)
    (hval : X p.val=0) (hder : fderiv ℂ X p.val=0) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  have he : a=fun _ => 1 := funext fun t => oneParameter_eq_one_of_generator_zero_jet
    hU a ha hc.isPreconnected hbd ha0 ham p hval hder t
  rw [he,infinitesimalGenerator_one]

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include Γ hhol

theorem isotropy_complete_generators_totally_real {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : U)
    (hXp : X p.val=0) (hYp : Y p.val=0)
    (hrel : fderiv ℂ Y p.val=Complex.I • fderiv ℂ X p.val) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  obtain ⟨b,hb,hb0,hbm,rfl⟩ := hY
  have hfixA := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hXp
  have hfixB := oneParameter_fixed_of_generator_zero hU b hb hbd hb0 hbm p hYp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  let B : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (b t).derivativeAt p
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  have hB0 : B 0=1 := by dsimp only [B]; rw [hb0,derivativeAt_one hU]
  have hAm (s t : ℝ) : A (s+t)=A s*A t := by
    dsimp only [A]
    rw [ham,derivativeAt_mul hU,hfixA]
    rfl
  have hAd (t : ℝ) : HasDerivAt A ((fderiv ℂ (infinitesimalGenerator a) p.val)*A t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfixA] at hd
    exact hd
  have hBd (t : ℝ) : HasDerivAt B ((Complex.I • fderiv ℂ (infinitesimalGenerator a) p.val)*B t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd b hb hb0 hbm t p
    rw [hfixB,hrel] at hd
    exact hd
  have hbounded : Bornology.IsBounded (Set.range (fun z : ℂ => A z.re*B z.im)) := by
    apply ((compact_faithful_isotropy hU hc.isPreconnected hbd Γ hhol p).1.isBounded).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨a z.re*b z.im,?_,?_⟩
    · change (a z.re).toHomeomorph ((b z.im).toHomeomorph p)=p
      rw [hfixB,hfixA]
    · change (a z.re*b z.im).derivativeAt p=A z.re*B z.im
      rw [derivativeAt_mul hU,hfixB]
      rfl
  have hz := bounded_complex_flow_generator_zero A B
    (fderiv ℂ (infinitesimalGenerator a) p.val) hA0 hB0 hAm hAd hBd hbounded
  exact IsCompleteGenerator.eq_zero_of_zero_jet hU hc hbd ⟨a,ha,ha0,ham,rfl⟩ p hXp hz
end Biholomorph
end Release061

end

end OAI
