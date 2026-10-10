import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.LocalTools
import OAI.Analysis.JiangSu.Comparison.FamilyExactLocalSupply

namespace OAI

section

noncomputable section
namespace FamilyComparison
open Pureness CurrentMain DirectComparison DirectPacking Filter
open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] {I : Type} [Nonempty I] (θ : I → TracialState A)
variable (U : Ultrafilter ℕ)
local notation "D" => FamilyUltrapower θ U
local notation "Λ" => familyLimitTrace θ U

@[instance_reducible] def limitTraceFamily : TraceFamily D where
  carrier := Set.range Λ

lemma limitTraceFamily_nonempty :
    let := limitTraceFamily θ U
    Nonempty (RestrictedTracialState D) := by
  let := limitTraceFamily θ U
  let s : ℕ → I := fun _ => Classical.ofNonempty
  exact ⟨⟨Λ s,⟨s,rfl⟩⟩⟩

lemma source_tools (hfree : (U : Filter ℕ) ≤ atTop)
    (hsupply : SpectralProjectionSupply Λ) :
    let := limitTraceFamily θ U
    SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)) ∧
      CoefficientSupply («D» := D) ∧ InsertionSupply («D» := D) := by
  let := limitTraceFamily θ U
  constructor
  · intro h hh hhn α hα hα1
    obtain ⟨p,hp,hl,hr,htr⟩ := hsupply h hh hhn α hα hα1
    refine ⟨p,hp,hl,hr,?_⟩
    rintro ⟨τ,⟨s,rfl⟩⟩
    exact htr s
  constructor
  · intro q hq s hs F ε hε
    obtain ⟨e,he,heq,ht⟩ := finite_coefficient_split Λ hsupply
      (fun q hq t ht => proportional_subprojection θ U hsupply hq ht) hq hs F hε
    refine ⟨e,he,heq,?_⟩
    intro b hb
    rintro ⟨τ,⟨t,rfl⟩⟩
    exact ht b hb t
  · intro z y hz hy
    obtain ⟨t,ht,htz,htr⟩ := FamilyComparison.orthogonal_insertion θ U hfree hsupply hz hy
    refine ⟨t,ht,htz,?_⟩
    rintro ⟨τ,⟨s,rfl⟩⟩
    exact htr s

end FamilyComparison

end
end

end OAI
