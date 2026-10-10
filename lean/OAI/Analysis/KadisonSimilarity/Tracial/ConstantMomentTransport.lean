import OAI.Analysis.KadisonSimilarity.FreeProduct.ConstantConjugateFreeness
import OAI.Analysis.KadisonSimilarity.Tracial.IntegerMomentMaps

namespace OAI

/-! A trace-preserving map reflects vanishing constant mixed moments. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (ht : ∀ a, τB (φ a) = τA a)

include ht in
theorem constantIntegerMoments_of_map (u : ℕ → unitary A)
    (hu : ConstantIntegerMoments τB hB ω trB (fun n => mapUnitary φ (u n))) :
    ConstantIntegerMoments τA hA ω trA u := by
  let Φ := tracialUltrapowerMap τA τB hA hB ω trA trB φ ht
  let F : A → Ultrapower τA hA ω trA := fun a => constant τA hA ω trA a - τA a • 1
  let G : B → Ultrapower τB hB ω trB := fun b => constant τB hB ω trB b - τB b • 1
  have hFG : Φ ∘ F = G ∘ φ := by
    funext a
    change Φ (constant τA hA ω trA a - τA a • 1) = G (φ a)
    simp only [Φ, G, map_sub, map_smul, map_one, tracialUltrapowerMap_constant, ht]
  intro a l hl hk
  have hzero := hu (a.map φ) (l.map (fun b => (b.1, b.2.map φ)))
    (admissibleIntTail_reindex φ l hl) (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hk c hc)
  change quotientTrace τB hB ω trB (integerEval G
    (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)))
    (a.map φ) (l.map (fun b => (b.1, b.2.map φ)))) = 0 at hzero
  rw [integerEval_reindex] at hzero
  change quotientTrace τA hA ω trA (integerEval F (quotientUnitary τA hA ω trA u) a l) = 0
  rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ ht,
    integerEval_hom, hFG, mapUnitary_tracialUltrapowerMap]
  exact hzero

end KadisonSimilarity

end

end OAI
