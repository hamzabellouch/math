import OAI.Analysis.KadisonSimilarity.Tracial.MatrixExpectationIdentification
import OAI.Analysis.BoundedHochschild.IncrementalPatching

namespace OAI

/-! Weak powers in a prescribed diffuse source, tested against ambient
coefficients. Conditional expectation moves only the coefficients. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance weakPowersSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

def sourceExpectation (a : M.toStarSubalgebra) : N.toStarSubalgebra :=
  ⟨(conditionalExpectation υ hNM a).val, conditionalExpectation_mem υ hNM a⟩

theorem sourceExpectation_pairing (a : M.toStarSubalgebra) (b : N.toStarSubalgebra) :
    υ.trace (a * coordinateInclusion hNM b) =
      vectorPositiveFunctional N υ.vector (sourceExpectation υ hNM a * b) := by
  have h := conditionalExpectation_orthogonal υ hNM a
    ⟨coordinateInclusion hNM b, b.property⟩
  have he : υ.trace (coordinateInclusion hNM b * a) =
      υ.trace (coordinateInclusion hNM b * conditionalExpectation υ hNM a) := by
    apply sub_eq_zero.mp
    simpa only [mul_sub, trace_sub] using h
  calc
    _ = υ.trace (coordinateInclusion hNM b * a) := υ.trace_mul_comm _ _
    _ = υ.trace (coordinateInclusion hNM b * conditionalExpectation υ hNM a) := he
    _ = υ.trace (conditionalExpectation υ hNM a * coordinateInclusion hNM b) :=
      υ.trace_mul_comm _ _
    _ = _ := rfl

/-- Every nonzero source corner contains a partial unitary whose prescribed
nonzero powers are weakly small against any finite family from the ambient algebra. -/
theorem exists_source_partial_unitary_weak_powers
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I] (a : I → M.toStarSubalgebra) (k : I → Bool × ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : PartialUnitary N.toStarSubalgebra, w.support = p ∧
      ∀ i, ‖υ.trace (a i * coordinateInclusion hNM (w.power (k i)))‖ <
        ε * (υ.trace (coordinateInclusion hNM p)).re := by
  let τN := restrictedTrace υ hNM
  let ρ := vectorPositiveFunctional N υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := τN.trace_mul_comm
  have hf (a : N.toStarSubalgebra) (ha : ρ (star a * a) = 0) : a = 0 := by
    apply τN.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace τN a a).trans ha)
  have hminimal : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  obtain ⟨w, hw, hweak⟩ := HochschildPatching.exists_partial_unitary_weak_powers p hp
    (concretePredualEquiv N) ρ (vectorPositiveFunctional_normal N υ.vector)
    (vectorPositiveFunctional_one N υ.vector υ.norm_vector) htr hf
    (fun b hb => hfactor b (fun x => (hb x).eq.symm)) hminimal hp0
    (fun i => sourceExpectation υ hNM (a i)) k hε
  refine ⟨w, hw, fun i => ?_⟩
  rw [sourceExpectation_pairing υ hNM]
  exact hweak i

end KadisonSimilarity

end

end OAI
