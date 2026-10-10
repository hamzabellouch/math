import OAI.Analysis.PureInfiniteness.FiniteRelativeSupport
import OAI.Analysis.PureInfiniteness.RelativeCornerSums
import OAI.Analysis.Nuclearity.PositiveMapAbelianization
import OAI.Analysis.PureInfiniteness.RelativeInnerCalculus

namespace OAI

/-! Finite merging of positive abelian-range maps. The orthogonality is
relative to finitely many positive values, so this construction works in the
nonunital ambient ultrapower without assuming a multiplier Cuntz family. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B J : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  [Fintype J] [DecidableEq J]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

/-- On any finite set, all matrix coefficients of a finite family can be
recovered from one positive abelian-range map. This is the local corner-sum
step in KR02 Lemma 7.16, with no unitality assumption on the ambient algebra. -/
theorem finite_abelian_merge (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) (T : J → B →L[ℂ] N)
    (hinner : ∀ j, ApproximatelyInnerAlong β (T j))
    (hpos : ∀ j b, 0 ≤ b → 0 ≤ T j b)
    (hcomm : ∀ j b c, Commute (T j b) (T j c)) (F : Finset B) :
    ∃ (R : B →L[ℂ] N) (r : J → N),
      ApproximatelyInnerAlong β R ∧ (∀ b, 0 ≤ b → 0 ≤ R b) ∧
      (∀ b c, Commute (R b) (R c)) ∧
      ∀ b ∈ F, ∀ i j, star (r i) * R b * r j = if i = j then T i b else 0 := by
  classical
  let P := F × Fin 4
  let b (p : P) : B := fourPositiveParts p.1.val p.2
  obtain ⟨r, _, hr⟩ := finite_relative_support_copies (M := J) U hP
    (fun jp : J × P => T jp.1 (b jp.2))
    (fun jp => hpos _ _ (fourPositiveParts_nonneg _ _))
  let S : B →L[ℂ] N := ∑ j, (ContinuousLinearMap.mulLeftRight ℂ N (r j) (star (r j))).comp (T j)
  have hS (x : B) : S x = relativeCornerSum r (fun j => T j x) := by
    simp only [S, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply, relativeCornerSum]
  have hSpos (x : B) (hx : 0 ≤ x) : 0 ≤ S x := by
    rw [hS]
    exact Finset.sum_nonneg (fun j _ => star_right_conjugate_nonneg (hpos j x hx) (r j))
  have hSinner : ApproximatelyInnerAlong β S := by
    have h := ApproximatelyInnerAlong.finset_sum β Finset.univ
      (fun j x => r j * T j x * star (r j)) (fun j _ => by
        simpa only [star_star] using (hinner j).outputCompression β (star (r j)))
    change ApproximatelyInnerAlong β (fun x => S x)
    simp_rw [hS]
    exact h
  have hScomm (p q : P) : Commute (S (b p)) (S (b q)) := by
    rw [hS, hS]
    exact relativeCornerSum_commute r _ _ (fun i j => hr i j (j, p))
      (fun i j => hr i j (j, q)) (fun j => hcomm j _ _)
  obtain ⟨z, _, hz, hRcomm⟩ := finite_positive_map_abelianization U hP S hSpos
    (fun p : P => S (b p)) (fun p => hSpos _ (fourPositiveParts_nonneg _ _)) hScomm
  let R : B →L[ℂ] N := (ContinuousLinearMap.mulLeftRight ℂ N (star z) z).comp S
  have hR (p : P) : R (b p) = S (b p) := hz p
  refine ⟨R, r, hSinner.outputCompression β z,
    fun x hx => star_left_conjugate_nonneg (hSpos x hx) z, hRcomm, ?_⟩
  intro x hx i j
  let L : B →L[ℂ] N := (ContinuousLinearMap.mulLeftRight ℂ N (star (r i)) (r j)).comp R
  let Q : B →L[ℂ] N := if i = j then T i else 0
  have hQ : Q x = if i = j then T i x else 0 := by
    by_cases hij : i = j <;> simp only [Q, hij, ite_true, ite_false,
      zero_apply]
  rw [← hQ]
  change L x = Q x
  apply linearMap_eq_of_fourPositiveParts L.toLinearMap Q.toLinearMap x
  intro k
  change star (r i) * R (b (⟨x, hx⟩, k)) * r j = Q (b (⟨x, hx⟩, k))
  rw [hR, hS, relativeCornerSum_coefficient r _
    (fun l => (hpos l _ (fourPositiveParts_nonneg _ _)).isSelfAdjoint)
    (fun l m n => hr l m (n, (⟨x, hx⟩, k)))]
  by_cases hij : i = j <;> simp only [Q, b, hij, ite_true, ite_false,
    zero_apply]

end WeakPureInfiniteness

end

end OAI
