import Mathlib
import OAI.Analysis.SymmetricDomains.PointSymmetryNegId
import OAI.Analysis.SymmetricDomains.InvolutionDerivativeNegId

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
namespace Release061

namespace Biholomorph

section
open Set Filter Topology
variable {n : ℕ} {U : Set (Affine n)}

theorem negative_derivative_of_pointSymmetry (hU : IsOpen U)
    (a : Biholomorph U U) (p : U)
    (hi : Function.Involutive a.toHomeomorph) (hfix : a.toHomeomorph p=p)
    (his : ∃ W : Set U, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, a.toHomeomorph q=q → q=p) :
    a.derivativeAt p = -1 := by
  apply involution_derivative_neg_id ((a.ambientAut_analytic hU _ p.property).hasStrictFDerivAt)
    (by simpa only [ambientAut_apply] using congrArg Subtype.val hfix)
  · filter_upwards [hU.mem_nhds p.property] with x hx
    rw [ambientAut_apply a ⟨x,hx⟩,ambientAut_apply a (a.toHomeomorph ⟨x,hx⟩),hi]
  · obtain ⟨W,hW,hp,hiso⟩ := his
    filter_upwards [(hU.isOpenMap_subtype_val W hW).mem_nhds ⟨p,hp,rfl⟩] with x hx hf
    obtain ⟨q,hq,rfl⟩ := hx
    have he : a.toHomeomorph q=q := Subtype.ext (by simpa only [ambientAut_apply] using hf)
    exact congrArg Subtype.val (hiso q hq he)

theorem boundedSymmetricDomain_iff_negative_isotropy (hU : IsOpen U)
    (hc : IsConnected U) (hb : Bornology.IsBounded U) :
    IsBoundedSymmetricDomain U ↔
      ∀ p : U, (-1 : Affine n →L[ℂ] Affine n) ∈
        (fun a : Biholomorph U U => a.derivativeAt p) '' {a | a.toHomeomorph p=p} := by
  constructor
  · intro h p
    obtain ⟨a,hi,hfix,his⟩ := h.2.2.2 p
    exact ⟨a,hfix,negative_derivative_of_pointSymmetry hU a p hi hfix his⟩
  · intro h
    refine ⟨hU,hc,hb,?_⟩
    intro p
    obtain ⟨a,hfix,hd⟩ := h p
    refine ⟨a,?_⟩
    apply a.pointSymmetry_of_neg_id hU hc.isPreconnected hb p hfix
    have hh := (a.ambientAut_analytic hU _ p.property).differentiableAt.hasFDerivAt
    change a.derivativeAt p = -1 at hd
    rwa [← derivativeAt,hd] at hh

end

open Set Filter Topology TopologicalSpace
variable {n : ℕ} {U : Set (Affine n)}

def isotropySubgroup (p : U) : Subgroup (Biholomorph U U) where
  carrier := {a | a.toHomeomorph p=p}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a.toHomeomorph (b.toHomeomorph p)=p
    exact congrArg a.toHomeomorph hb |>.trans ha
  inv_mem' := by
    intro a ha
    change a.toHomeomorph.symm p=p
    apply a.toHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    exact ha.symm

def isotropyRepresentation (hU : IsOpen U) (p : U) :
    isotropySubgroup p →* (Affine n →L[ℂ] Affine n) where
  toFun := fun a => a.val.derivativeAt p
  map_one' := derivativeAt_one hU p
  map_mul' := by
    intro a b
    change (a.val*b.val).derivativeAt p=a.val.derivativeAt p*b.val.derivativeAt p
    rw [derivativeAt_mul hU,b.property]
    rfl

def isotropyRepresentationUnits (hU : IsOpen U) (p : U) :
    isotropySubgroup p →* (Affine n →L[ℂ] Affine n)ˣ :=
  (isotropyRepresentation hU p).toHomUnits

@[simp] theorem isotropyRepresentationUnits_val (hU : IsOpen U) (p : U)
    (a : isotropySubgroup p) :
    (isotropyRepresentationUnits hU p a : Affine n →L[ℂ] Affine n)=a.val.derivativeAt p := rfl

theorem isotropyRepresentation_injective (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (p : U) :
    Function.Injective (isotropyRepresentation hU p) := by
  intro a b hab
  apply Subtype.ext
  apply firstJet_injective hU hc hb p
  exact Prod.ext (a.property.trans b.property.symm) hab

theorem isotropyRepresentationUnits_injective (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (p : U) :
    Function.Injective (isotropyRepresentationUnits hU p) := by
  intro a b hab
  exact isotropyRepresentation_injective hU hc hb p
    (congrArg (fun a : (Affine n →L[ℂ] Affine n)ˣ => a.val) hab)

theorem isotropyRepresentation_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (isotropyRepresentation hU p) :=
  (derivativeAt_continuous hU p).comp continuous_subtype_val

theorem isotropyRepresentationUnits_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (isotropyRepresentationUnits hU p) := by
  apply Units.continuous_iff.mpr
  refine ⟨isotropyRepresentation_continuous hU p,?_⟩
  exact (isotropyRepresentation_continuous hU p).comp continuous_inv

theorem isotropyRepresentationUnits_compact_embedding (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    CompactSpace (isotropySubgroup p) ∧ IsClosedEmbedding (isotropyRepresentationUnits hU p) := by
  let hcpt : CompactSpace (isotropySubgroup p) :=
    isCompact_iff_compactSpace.mp (compact_stabilizer hU hc hb Γ hhol p)
  exact ⟨hcpt,(isotropyRepresentationUnits_continuous hU p).isClosedEmbedding
    (isotropyRepresentationUnits_injective hU hc hb p)⟩

end Biholomorph
end Release061

end

end OAI
