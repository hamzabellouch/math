import OAI.Analysis.PureInfiniteness.UltrapowerCopiesExact
import OAI.Analysis.Nuclearity.FourPositiveParts
import OAI.Analysis.PureInfiniteness.CommutativeCoefficientAlgebra
import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! Relative copies on a finite family from a commutative C*-algebra, and
hence on finite commuting normal families in the original ultrapower. -/

noncomputable section
open Filter
open scoped IsMulCommutative

namespace WeakPureInfiniteness

variable {A C I M : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCommCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem relative_copies_on_commutative_family (hP : MainGap.PropertyP A)
    (φ : C →⋆ₙₐ[ℂ] N) (c : I → C) :
    ∃ v : M → N, (∀ j, ‖v j‖ ≤ 1) ∧ (∀ i j, Commute (φ (c i)) (v j)) ∧
      ∀ i j k, (star (v j) * v k) * φ (c i) = if j = k then φ (c i) else 0 := by
  let a (p : I × Fin 4) := φ (fourPositiveParts (c p.1) p.2)
  have ha (p : I × Fin 4) : 0 ≤ a p := map_nonneg φ (fourPositiveParts_nonneg _ _)
  have hc (p q : I × Fin 4) : Commute (a p) (a q) := (Commute.all _ _).map φ
  obtain ⟨v, hv, hcomm, hrel⟩ := ultrapower_relative_copies (M := M) U hP a ha hc
  refine ⟨v, hv, ?_, ?_⟩
  · intro i j
    let f := ((ContinuousLinearMap.mul ℂ N).flip (v j)).comp (starHomContinuousLinear φ)
    let g := (ContinuousLinearMap.mul ℂ N (v j)).comp (starHomContinuousLinear φ)
    exact linearMap_eq_of_fourPositiveParts f.toLinearMap g.toLinearMap (c i)
      (fun k => (hcomm (i, k) j).eq)
  · intro i j k
    let f := (ContinuousLinearMap.mul ℂ N (star (v j) * v k)).comp (starHomContinuousLinear φ)
    by_cases hjk : j = k
    · simp only [ite_eq_left hjk]
      exact linearMap_eq_of_fourPositiveParts f.toLinearMap
        (starHomContinuousLinear φ).toLinearMap (c i)
        (fun l => by
          change (star (v j) * v k) * φ (fourPositiveParts (c i) l) =
            φ (fourPositiveParts (c i) l)
          simpa only [a, ite_eq_left hjk] using hrel (i, l) j k)
    · simp only [ite_eq_right hjk]
      exact linearMap_eq_of_fourPositiveParts f.toLinearMap (0 : C →ₗ[ℂ] N) (c i)
        (fun l => by
          change (star (v j) * v k) * φ (fourPositiveParts (c i) l) = 0
          simpa only [a, ite_eq_right hjk] using hrel (i, l) j k)

end WeakPureInfiniteness

end

end OAI
