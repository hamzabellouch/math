import OAI.Analysis.KadisonSimilarity.Tracial.SourceQuotientMoments
import OAI.Analysis.KadisonSimilarity.Tracial.SourceUltrapowerInclusion

namespace OAI

/-! All mixed words from a countable ambient family vanish for a sequence
of source unitaries in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance allMomentAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance allMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

include hfactor hdiff hirr in
theorem exists_source_quotient_unitary_all_moments
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {I : Type*} [Countable I] [Nonempty I]
    (A : I → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      AllQuotientMoments (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        A (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  classical
  let τ := vectorPositiveFunctional M υ.vector
  let h1 : τ 1 = 1 := υ.trace_one
  let tr : ∀ a b, τ (a * b) = τ (b * a) := υ.trace_mul_comm
  let : Inhabited I := ⟨Classical.arbitrary I⟩
  let : Encodable I := Encodable.ofCountable I
  let f : ℕ → I := fun n => (Encodable.decode (α := I) n).getD default
  have hf (i : I) : f (Encodable.encode i) = i := by simp [f]
  obtain ⟨u, hu⟩ := exists_source_quotient_unitary_moments υ hRM hfactor hdiff hirr ω hω
    (A ∘ f) (fun i n => hA (f i) n)
  refine ⟨u, fun K a l hl => ?_⟩
  let C : ℕ → Ultrapower (A := M.toStarSubalgebra) τ h1 ω tr := fun n => quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A (f n)) -
    quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr (quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A (f n))) • 1
  have hz := all_finite_words (quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr) C
    (quotientUnitary (M := M.toStarSubalgebra) τ h1 ω tr (fun n => mapUnitary (coordinateInclusion hRM) (u n)))
    hu K (a.map Encodable.encode) (l.map (mapAtom Encodable.encode id))
    (admissibleTail_map Encodable.encode id l hl)
  rw [mixedEval_map C Encodable.encode id (fun _ => rfl)] at hz
  have hc : C ∘ Encodable.encode = fun i => quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A i) -
      quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr (quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A i)) • 1 := by
    funext i
    simp only [Function.comp_apply, C, hf]
  rw [hc] at hz
  exact hz

end KadisonSimilarity

end

end OAI
