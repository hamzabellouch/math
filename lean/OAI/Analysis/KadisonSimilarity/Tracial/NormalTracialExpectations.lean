import OAI.Analysis.KadisonSimilarity.Representation.GeneratedNormalRange

namespace OAI

/-! Trace-preserving expectations on the actual normal subalgebras of a
faithful tracial geometry, including its constructed L²-generated algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem tracialExpectation_of_normal_range
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) (N : VonNeumannAlgebra H)
    (hSrange : S.map G.left = N.toStarSubalgebra) :
    Nonempty (TracialExpectation G.trace S) := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  have hNM : N ≤ M := by
    intro T hT
    change T ∈ M.toStarSubalgebra
    rw [← hrange]
    change T ∈ N.toStarSubalgebra at hT
    rw [← hSrange] at hT
    obtain ⟨a, _, rfl⟩ := hT
    exact ⟨a, rfl⟩
  have he : (insideAlgebra (M := M) (P := N)).comap e.toStarAlgHom = S := by
    ext a
    change G.left a ∈ N.toStarSubalgebra ↔ a ∈ S
    rw [← hSrange]
    constructor
    · rintro ⟨b, hb, heq⟩
      exact (G.left_injective hf heq) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  have E := (concreteTracialExpectation τ hNM).comapEquiv e
    (fun a => G.normalTracialRepresentation_trace h1 hf M hrange a)
  rw [he] at E
  exact ⟨E⟩

theorem l2Generated_tracialExpectation
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) :
    Nonempty (TracialExpectation G.trace (G.l2GeneratedAlgebra S)) := by
  obtain ⟨N, hN⟩ := G.exists_l2Generated_normal_range h1 hf M hrange S
  exact G.tracialExpectation_of_normal_range h1 hf M hrange _ N hN

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
