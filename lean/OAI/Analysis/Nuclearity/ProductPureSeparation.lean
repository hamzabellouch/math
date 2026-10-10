import OAI.Analysis.Nuclearity.ProductStateIdealExcision
import OAI.Analysis.Nuclearity.ElementaryGeneratedIdeal

namespace OAI

/-! The implication from product-pure-state ideal separation to elementary
ideal generation (Tomiyama, Tohoku Math. J. 19 (1967), Theorem 5, combined
with pure-state excision). The separation property is an explicit
hypothesis of this implication. -/

noncomputable section
open scoped ComplexOrder Topology

namespace WeakPureInfiniteness

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

structure ProductPureFunctional where
  leftState : A →ₚ[ℂ] ℂ
  rightState : B →ₚ[ℂ] ℂ
  left_one : leftState 1 = 1
  right_one : rightState 1 = 1
  left_pure : PureStateExcision.ofPositiveState leftState left_one ∈
    (PureStateExcision.realStateCarrier (A := A)).extremePoints ℝ
  right_pure : PureStateExcision.ofPositiveState rightState right_one ∈
    (PureStateExcision.realStateCarrier (A := B)).extremePoints ℝ
  functional : MinimalTensor A B →L[ℂ] ℂ
  norm_le_one : ‖functional‖ ≤ 1
  elementary : ∀ a b, functional (minimalElementary a b) = leftState a * rightState b

/-- The product-pure-state separation condition in Tomiyama's Theorem 5. -/
def ProductPureStateSeparation : Prop :=
  ∀ (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) (z : MinimalTensor A B),
    z ∉ J.module → ∃ F : ProductPureFunctional A B,
      (∀ x ∈ J.module, F.functional x = 0) ∧ F.functional z ≠ 0

variable {A B}

theorem elementary_ideal_generation_of_product_pure_separation
    (hsep : ProductPureStateSeparation A B)
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    (elementaryGeneratedIdeal J).module = J.module := by
  apply le_antisymm (elementaryGeneratedIdeal_le J)
  intro z hz
  by_contra hnot
  obtain ⟨F, hkill, hdetect⟩ := hsep (elementaryGeneratedIdeal J) z hnot
  let Q := NonunitalClosedIdeal.QuotientAlgebra J
  let _ : PartialOrder Q := CStarAlgebra.spectralOrder Q
  let _ : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing Q
  let q : MinimalTensor A B →⋆ₙₐ[ℂ] Q := NonunitalClosedIdeal.QuotientAlgebra.mkHom J
  have hq (x : MinimalTensor A B) : q x = 0 ↔ x ∈ J.module := by
    change NonunitalClosedIdeal.QuotientAlgebra.mk J x =
      NonunitalClosedIdeal.QuotientAlgebra.mk J 0 ↔ _
    simpa only [sub_zero] using NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff J x 0
  have hzero (a : A) (b : B) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
      (hab : q (minimalElementary a b) = 0) : F.functional (minimalElementary a b) = 0 :=
    hkill _ (elementary_mem_generatedIdeal J a b ((hq _).mp hab))
  exact hdetect (pure_product_vanishes_on_kernel q F.leftState F.rightState
    F.left_one F.right_one F.left_pure F.right_pure F.functional F.norm_le_one
    F.elementary hzero z ((hq z).mpr hz))

theorem elementary_span_of_product_pure_separation
    (hsep : ProductPureStateSeparation A B)
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (z : MinimalTensor A B) (hz : z ∈ J.module) :
    z ∈ closure (Submodule.span ℂ {w : MinimalTensor A B |
      ∃ a b, w = minimalElementary a b ∧ w ∈ J.module} : Set (MinimalTensor A B)) := by
  change z ∈ (elementaryGeneratedIdeal J).module
  rw [elementary_ideal_generation_of_product_pure_separation hsep J]
  exact hz

end WeakPureInfiniteness

end

end OAI
