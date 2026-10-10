import OAI.GroupTheory.PolycyclicRecognition.Algebra.OpenProductRepresentation

namespace OAI

/-! # Descent while retaining explicit factor-coordinate formulas -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G A X Y : Type*} [Group N] [Group D] [Group G] [Group A]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G] [TopologicalSpace A]
  [ContinuousMul G] [ContinuousMul A]

theorem exists_representation_with_factor_coordinates
    (φ : D →* MulAut N) (iN : N →* G) (iD : D →* G)
    (hiN : Continuous iN) (hiD : Continuous iD)
    (hbase : ∀ d, iN.comp (φ d).toMonoidHom =
      (MulAut.conj (iD d)).toMonoidHom.comp iN)
    (hs : Function.Surjective (fun p : N × D => iN p.1 * iD p.2))
    (ho : IsOpenMap (fun p : N × D => iN p.1 * iD p.2))
    (nExp : X → N) (dExp : Y → D) (nVal : X → A) (dVal : Y → A)
    (hn : ∃ fN : N →* A, Continuous fN ∧ ∀ x, fN (nExp x) = nVal x)
    (hd : ∃ fD : D →* A, Continuous fD ∧ ∀ y, fD (dExp y) = dVal y)
    (hrelations : ∀ (fN : N →* A) (fD : D →* A),
      (∀ x, fN (nExp x) = nVal x) → (∀ y, fD (dExp y) = dVal y) →
        (∀ d n, fN (φ d n) = fD d * fN n * (fD d)⁻¹) ∧
        (∀ n d, iN n = iD d → fN n = fD d)) :
    ∃ f : G →* A, Continuous f ∧
      ∀ x y, f (iN (nExp x) * iD (dExp y)) = nVal x * dVal y := by
  obtain ⟨fN,hfN,heN⟩ := hn
  obtain ⟨fD,hfD,heD⟩ := hd
  obtain ⟨hc,ha⟩ := hrelations fN fD heN heD
  obtain ⟨f,hf,he⟩ := exists_continuous_representation_of_open_factor_maps
    φ iN iD hiN hiD hbase hs ho fN fD hfN hfD hc ha
  exact ⟨f,hf,fun x y => (he _ _).trans (by rw [heN,heD])⟩

end PolycyclicRecognition

end

end OAI
