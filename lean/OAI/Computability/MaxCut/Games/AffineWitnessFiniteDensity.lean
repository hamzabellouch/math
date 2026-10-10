import Mathlib
import OAI.Computability.MaxCut.Encoding.AffineWitnessFirstBit

namespace OAI

/-!
# Finite indicator expectations as conditional cardinality ratios

These identities use the complete finite sample set in the denominator.  They
also cover the empty set, for which both the expectation and the ratio are zero.
The equivalence variant transfers both the event and the sample space, so no
conditioning factor is lost when changing representations of a slice.
-/

namespace MaxCutGames.Inverse

open scoped BigOperators

variable {X Y : Type*}

/-- Filtering a finite sample set counts the same objects as first restricting
to the sample set and then imposing the event predicate. -/
theorem card_finset_subtype_eq_filter_card (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    Nat.card {x : s // p x.val} = (s.filter p).card := by
  classical
  let e : {x : s // p x.val} ≃ ↥(s.filter p) :=
    { toFun := fun x =>
        ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x =>
        ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
          (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

/-- An indicator's expectation on a finite set is its agreement count divided
by the cardinality of that same finite set. -/
theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

/-- A bijection preserving the event preserves its count. No choice of a
`Fintype` enumeration is involved in this identity. -/
theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

/-- Transfer the indicator expectation through an equivalence of the complete
finite sample space, including the denominator of the conditional law. -/
theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end MaxCutGames.Inverse

/-! First-bit normalization in the actual finite-array shortcode API. The
sample space, event count, affine intercept, and folding law are transported
exactly; no inverse result is assumed by the representation bridge. -/

namespace MaxCutGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

/-- The coordinate row of a binary linear functional. -/
def functionalRow (e : Vector m →ₗ[F2] F2) : Vector m :=
  fun j => e (Pi.single j 1)

theorem toMatrix_shift (e : Vector m →ₗ[F2] F2) (h : Vector ell)
    (M : Mat ell m) :
    LinearMap.toMatrix' (AffineWitness.shift e h (Matrix.toLin' M)) =
      M + rankOne h (functionalRow e) := by
  rw [AffineWitness.shift, map_add, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.smulRight_apply,
    Pi.smul_apply, smul_eq_mul, rankOne, functionalRow, mul_comm]

namespace Slice

/-- Exact density identity on the complete nonempty affine slice, with no
lost conditioning factor in the change from matrices to linear maps. -/
theorem affineAgreement_eq_linear_ratio (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u =
      (Nat.card {N : AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) //
        f (LinearMap.toMatrix' N.val) = N.val z + u} : ℝ) /
      (Nat.card (AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀)) : ℝ) := by
  unfold affineAgreement
  apply finset_expect_indicator_eq_card_ratio_of_equiv S.points
    (fun M => f M = evaluate M z + u) (S.linearSliceEquiv M₀ hM₀)
    (fun N => f (LinearMap.toMatrix' N.val) = N.val z + u)
  intro M
  change (f M.val = evaluate M.val z + u) ↔
    (f (LinearMap.toMatrix' (Matrix.toLin' M.val)) = Matrix.toLin' M.val z + u)
  rw [LinearMap.toMatrix'_toLin']
  rfl

/-- First-bit normalization for the exact selected shortcode slice.
The original affine agreement is preserved, not merely bounded below. -/
theorem first_bit_normalization (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (e : Vector m →ₗ[F2] F2)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell)
    (hfold : ∀ (h : S.rowMap.ker) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (α : ℝ) (hα : 0 < α) (hgood : α / 2 ≤ S.affineAgreement f z u)
    (hsmall : 1 / (2 : ℝ) ^ (ell - S.rows) < α / 8) :
    ∃ z' : Vector m, ∃ u' : Vector ell, e z' = 1 ∧
      S.affineAgreement f z' u' = S.affineAgreement f z u ∧
      ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u := by
  let F : (Vector m →ₗ[F2] Vector ell) → Vector ell :=
    fun N => f (LinearMap.toMatrix' N)
  have hfold' : ∀ (h : S.rowMap.ker) N,
      F (AffineWitness.shift e h N) = F N + h := by
    intro h N
    have hs : LinearMap.toMatrix' (AffineWitness.shift e h N) =
        LinearMap.toMatrix' N + rankOne h (functionalRow e) := by
      simpa only [Matrix.toLin'_toMatrix'] using toMatrix_shift e h (LinearMap.toMatrix' N)
    exact (congrArg f hs).trans (hfold h (LinearMap.toMatrix' N))
  have hgood' := hgood
  rw [S.affineAgreement_eq_linear_ratio M₀ hM₀ f z u] at hgood'
  obtain ⟨z', u', he, ht⟩ := AffineWitness.first_bit_witness e S.rowMap S.columnSpan
    (Matrix.toLin' M₀) z u F hfold' α hα hgood' hsmall
  refine ⟨z', u', he, S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z z' u u' ht, ?_⟩
  intro M hM
  exact ht (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end MaxCutGames.Inverse.Shortcode

end OAI
