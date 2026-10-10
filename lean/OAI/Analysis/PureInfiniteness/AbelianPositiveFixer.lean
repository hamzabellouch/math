import OAI.Analysis.PureInfiniteness.AbelianRangeExtension
import OAI.Analysis.PureInfiniteness.CommutativeCoefficientAlgebra
import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! The point-fixing input to KR02 Lemma 7.18: every positive element of the
separable subalgebra is fixed by an actual abelian-range inner compression. -/

noncomputable section
open scoped IsMulCommutative

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem abelian_range_compression_fixing_positive (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) (b : B) (hb : 0 ≤ b) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ innerHomCompression β v b = β b ∧
      ∀ x y, Commute (innerHomCompression β v x) (innerHomCompression β v y) := by
  let c : Unit → B := fun _ => b
  let C := coefficientAlgebra c
  have hsa := hb.isSelfAdjoint
  let : IsMulCommutative C := coefficientAlgebra_commutative c
    (fun _ => hsa.isStarNormal) (fun _ _ => Commute.refl _)
    (fun _ _ => by rw [hsa.star_eq])
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let γ := β.comp (NonUnitalStarSubalgebraClass.subtype C)
  obtain ⟨v, hv, hfix, hcomm⟩ := exists_abelian_range_compression U hP β γ
  refine ⟨v, hv, ?_, hcomm⟩
  exact hfix (coefficientGenerator c ())

end WeakPureInfiniteness

end

end OAI
