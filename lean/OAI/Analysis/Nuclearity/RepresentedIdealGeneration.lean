import OAI.Analysis.Nuclearity.RepresentedIdealSeparation
import OAI.Analysis.Nuclearity.IdealSeparatingRepresentation

namespace OAI

/-! The Tomiyama factor-image argument followed by pure-state excision.
The hypothesis is nuclearity of represented quotients of the left factor
(Choi–Effros, Duke Math. J. 43 (1976), Corollary 3.3). -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem elementary_generation_of_represented_nuclearity
    (hN : ∀ (H : ComplexHilbert.{u+1})
      (π : UnitalTensorRepresentation (A := A) (B := B) (H := H)),
      (∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ c : ℂ, T = c • 1) →
      Pureness.IsNuclear.{u+1,u+1} (representedAlgebra (leftRepresentedMap π)))
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    (elementaryGeneratedIdeal J).module = J.module := by
  apply le_antisymm (elementaryGeneratedIdeal_le J)
  intro z hz
  by_contra hnot
  have hrep : ∃ H : ComplexHilbert.{u+1},
      ∃ π : UnitalTensorRepresentation (A := A) (B := B) (H := H),
      (∀ a ∈ (elementaryGeneratedIdeal J).module, π a = 0) ∧ π z ≠ 0 ∧
      ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1 := by
    let _ : CStarAlgebra (MinimalTensor A B) := minimalTensorUnitalStructure A B
    exact exists_ideal_separating_irreducible (elementaryGeneratedIdeal J) z hnot
  obtain ⟨H, π, hI, hπz, hs⟩ := hrep
  obtain ⟨F, hkill, y, hy, hdetect⟩ := productPure_separates_ideals_of_representation
    (elementaryGeneratedIdeal J) J H π
    (representedImageData (leftRepresentedMap π))
    (representedImageData (rightRepresentedMap π)) hs (hN H π hs) hI z hz hπz
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
    F.elementary hzero y ((hq y).mpr hy))

end WeakPureInfiniteness

end

end OAI
