import OAI.Analysis.KadisonSimilarity.Tracial.TracialNormalSpan
import OAI.Analysis.KadisonSimilarity.Tracial.TracialInputTransport
import OAI.Analysis.KadisonSimilarity.Tracial.TracialL2Closure
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralCutMoments

namespace OAI

/-! A tracial Hilbert geometry with faithful normal left range supplies the
concrete vector-trace model used in the discharged tracial inputs. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem trace_eq_vectorTrace (a : A) :
    vectorTrace (G.vector 1) (G.left a) = G.trace a := by
  rw [vectorTrace_apply, G.left_vector, mul_one, G.inner_vector, star_one, one_mul]

theorem norm_identityVector (h1 : G.trace 1 = 1) : ‖G.vector 1‖ = 1 := by
  have h := G.inner_vector 1 1
  rw [star_one, one_mul, h1] at h
  have hn : ‖G.vector 1‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
    rfl
  nlinarith [norm_nonneg (G.vector 1)]

def normalTracialRepresentation (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) : TracialRepresentation M := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  refine {
    vector := G.vector 1
    norm_vector := G.norm_identityVector h1
    cyclic := ?_
    separating := ?_
  }
  · intro S T
    obtain ⟨a, rfl⟩ := e.surjective S
    obtain ⟨b, rfl⟩ := e.surjective T
    change inner ℂ (G.vector 1) (G.left a (G.left b (G.vector 1))) =
      inner ℂ (G.vector 1) (G.left b (G.left a (G.vector 1)))
    simp only [G.left_vector, mul_one, G.inner_vector, star_one, one_mul]
    exact G.tracial a b
  · intro T hT
    obtain ⟨a, rfl⟩ := e.surjective T
    have ha : G.vector a = 0 := by
      change G.left a (G.vector 1) = 0 at hT
      simpa only [G.left_vector, mul_one] using hT
    have haz : a = 0 := hf (ha.trans (map_zero G.vector).symm)
    rw [haz, map_zero]

@[simp] theorem normalTracialRepresentation_vector (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) :
    (G.normalTracialRepresentation h1 hf M hrange).vector = G.vector 1 := rfl

@[simp] theorem normalTracialRepresentation_trace (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) (a : A) :
    (G.normalTracialRepresentation h1 hf M hrange).trace
      (equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange a) = G.trace a := by
  change vectorTrace (G.vector 1) (G.left a) = G.trace a
  exact G.trace_eq_vectorTrace a

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
