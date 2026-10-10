import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.FiniteCentral
import OAI.Analysis.JiangSu.Comparison.FamilyLocalTools

namespace OAI

section

noncomputable section
namespace FamilyComparison
open Pureness CurrentMain DirectComparison DirectPacking Filter
open scoped ComplexOrder

section Source
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] {I : Type} [Nonempty I] (θ : I → TracialState A)
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsupply : SpectralProjectionSupply (familyLimitTrace θ U)) (hnuc : IsNuclear A)
local notation "D" => FamilyUltrapower θ U
local notation "Λ" => familyLimitTrace θ U
local notation "ι" => familyUltrapowerMap θ U

include hfree hsupply hnuc in

theorem comparison_finite_central_splitting
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : D, IsStarProjection p ∧ ∀ u ∈ K,
      familyTwoNorm Λ (p*ι (u:A)-ι (u:A)*p) < ε ∧
      familyTraceNorm Λ (p*ι (u:A)-(1/2:ℂ) • ι (u:A)) < ε := by
  let := limitTraceFamily θ U
  let := limitTraceFamily_nonempty θ U
  obtain ⟨hs,hc,hi⟩ := source_tools θ U hfree hsupply
  obtain ⟨p,hp,ht⟩ := finite_set_central_splitting ι hnuc hs hc hi K hε
  refine ⟨p,hp,?_⟩
  intro u hu
  have h2 (a : D) : familyTwoNorm Λ a ≤
      familyTwoNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceTwoNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D))
      ⟨Λ s,⟨s,rfl⟩⟩ a
  have h1 (a : D) : familyTraceNorm Λ a ≤
      familyTraceNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D))
      ⟨Λ s,⟨s,rfl⟩⟩ a
  exact ⟨(h2 _).trans_lt (ht u hu).1,(h1 _).trans_lt (ht u hu).2⟩

end Source
end FamilyComparison

end
end

end OAI
