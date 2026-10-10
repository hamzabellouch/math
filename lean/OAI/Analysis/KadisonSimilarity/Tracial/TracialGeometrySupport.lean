import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry

namespace OAI

/-! The normal tracial geometry supplies the propagation support input.
Positivity of its trace follows directly from the Hilbert inner product. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

section Ordered
variable [PartialOrder A] [StarOrderedRing A]

def positiveTrace : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ G.trace (fun a ha => by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    rw [← G.inner_vector]
    exact Complex.nonneg_iff.mpr ⟨inner_self_nonneg (𝕜 := ℂ) (x := G.vector b), (inner_self_im (𝕜 := ℂ) (G.vector b)).symm⟩)

@[simp] theorem positiveTrace_apply (a : A) : G.positiveTrace a = G.trace a := rfl

end Ordered

theorem rightSupportInput_of_normal_range
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (q : A) (hq : IsStarProjection q) (S : StarSubalgebra ℂ A) :
    TracialRightSupportInput (fun a => (G.trace a).re) q S := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact tracialRightSupportInput_of_concrete_range M G.positiveTrace G.tracial
    G.left (G.left_injective hf) hrange q hq S

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
