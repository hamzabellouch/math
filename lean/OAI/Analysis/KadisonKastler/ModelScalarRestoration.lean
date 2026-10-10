import OAI.Analysis.KadisonKastler.ModelWordExpansion
import OAI.Analysis.KadisonKastler.SubwordExpansion

namespace OAI

/-!
# Scalar restoration for actual free projection words

Copy positions are injective, but their labels may repeat. The centered
subword estimate therefore uses positions as its indices. This gives
scalar restoration for each word and for any family of at most `r!`
label functions, including the full family of orderings of a distinct
label set.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

namespace FreeDiagonalModel

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : FreeDiagonalModel ι α H)

def projectionWord {r : ℕ} (position : Fin r → ι) (label : Fin r → α) : H →L[ℂ] H :=
  tupleOperatorProduct (fun i => M.e (position i)) label

def centeredLabelWord {r : ℕ} (position : Fin r → ι) (label : Fin r → α) : H →L[ℂ] H :=
  tupleOperatorProduct (fun i => M.centered (position i)) label

/-- The labels need not be distinct: the four zero products only use
the injectivity of the copy positions. This also applies to each subword. -/
theorem norm_centered_position_word_le {r : ℕ} (position : Fin r → ι)
    (hposition : Function.Injective position) (label : Fin r → α)
    (l : List (Fin r)) (hl : l.Nodup) :
    ‖orderedWord (fun i => M.centered (position i) (label i)) l‖ ≤
      (2 * l.length + 1 : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ (l.length - 1)) := by
  have he : orderedWord (fun i => M.centered (position i) (label i)) l =
      centeredLetterProduct (fun i => M.C (position i) (label i))
        (fun i => M.D (position i) (label i))
        (fun i => star (M.C (position i) (label i))) l := by
    unfold orderedWord centeredLetterProduct
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact M.centered_eq (position i) (label i)
  rw [he]
  apply norm_centeredLetterProduct_le_inv_sqrt
  · intro i j hij
    exact M.star_creation_mul_creation (fun h => hij (hposition h)) (label i) (label j)
  · intro i j hij
    exact M.star_creation_mul_D (fun h => hij (hposition h)) (label i) (label j)
  · intro i j hij
    exact M.D_mul_creation (fun h => hij (hposition h)) (label i) (label j)
  · intro i j hij
    exact M.D_mul_D (fun h => hij (hposition h)) (label i) (label j)
  · exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  · exact ContinuousLinearMap.norm_id_le
  · intro i
    exact M.norm_creation_le (position i) (label i)
  · intro i
    exact M.norm_D_le (position i) (label i)
  · intro i
    exact M.norm_star_creation_le (position i) (label i)
  · exact hl

theorem norm_centeredLabelWord_le {r : ℕ} (position : Fin r → ι)
    (hposition : Function.Injective position) (label : Fin r → α) :
    ‖M.centeredLabelWord position label‖ ≤
      (2 * r + 1 : ℝ) / Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
  have h := M.norm_centered_position_word_le position hposition label
    (List.ofFn id) (List.nodup_ofFn_ofInjective Function.injective_id)
  simpa only [centeredLabelWord, tupleOperatorProduct, orderedWord,
    List.map_ofFn, Function.comp_def, id_eq, List.length_ofFn] using h

/-- Restoring the scalar part of each letter in a single actual word. -/
theorem norm_projectionWord_sub_centeredLabelWord_le {r : ℕ} (hr : 0 < r)
    (position : Fin r → ι) (hposition : Function.Injective position)
    (label : Fin r → α) :
    ‖M.projectionWord position label - M.centeredLabelWord position label‖ ≤
      1 / (Fintype.card α : ℝ) ^ r +
        ∑ k ∈ Ico 1 r, (r.choose k : ℝ) *
          ((2 * k + 1 : ℝ) / ((Fintype.card α : ℝ) ^ (r - k) *
            Real.sqrt ((Fintype.card α : ℝ) ^ (k - 1)))) := by
  have hd : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  have he : ∀ i ∈ List.ofFn (id : Fin r → Fin r),
      M.e (position i) (label i) = M.centered (position i) (label i) +
        (1 / (Fintype.card α : ℝ)) • (1 : H →L[ℂ] H) := by
    intro i _
    simp only [centered, one_div, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv,
      RCLike.ofReal_natCast, sub_add_cancel]
  have hc : ∀ w, List.Sublist w (List.ofFn (id : Fin r → Fin r)) →
      0 < w.length →
      ‖orderedWord (fun i => M.centered (position i) (label i)) w‖ ≤
        (2 * w.length + 1 : ℝ) /
          Real.sqrt ((Fintype.card α : ℝ) ^ (w.length - 1)) := by
    intro w hw _
    exact M.norm_centered_position_word_le position hposition label w
      (List.Nodup.sublist hw (List.nodup_ofFn_ofInjective Function.injective_id))
  have h := norm_orderedWord_sub_centered_le
    (fun i => M.e (position i) (label i)) (fun i => M.centered (position i) (label i))
    hd ContinuousLinearMap.norm_id_le (List.ofFn id)
    (by simpa only [List.length_ofFn] using hr) he hc
  simpa only [projectionWord, centeredLabelWord, tupleOperatorProduct, orderedWord,
    List.map_ofFn, Function.comp_def, id_eq, List.length_ofFn] using h

/-- At most `r!` label functions suffice; no distinctness of their
labels is used in the restoration estimate. -/
theorem norm_sum_projectionWord_sub_centeredLabelWord_le {τ : Type*} {r : ℕ}
    (hr : 0 < r) (position : Fin r → ι) (hposition : Function.Injective position)
    (T : Finset τ) (label : τ → Fin r → α) (hcard : T.card ≤ r.factorial) :
    ‖(∑ t ∈ T, M.projectionWord position (label t)) -
        ∑ t ∈ T, M.centeredLabelWord position (label t)‖ ≤
      scalarRestorationBound r (Fintype.card α) := by
  let R : ℝ := 1 / (Fintype.card α : ℝ) ^ r +
    ∑ k ∈ Ico 1 r, (r.choose k : ℝ) *
      ((2 * k + 1 : ℝ) / ((Fintype.card α : ℝ) ^ (r - k) *
        Real.sqrt ((Fintype.card α : ℝ) ^ (k - 1))))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ T, ‖M.projectionWord position (label t) -
          M.centeredLabelWord position (label t)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ T, R := sum_le_sum (fun t _ =>
      M.norm_projectionWord_sub_centeredLabelWord_le hr position hposition (label t))
    _ = (T.card : ℝ) * R := by simp
    _ ≤ (r.factorial : ℝ) * R :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hR
    _ = scalarRestorationBound r (Fintype.card α) := rfl

/-- Apply scalar restoration to all orderings of an `r`-element set. -/
theorem norm_sum_distinct_projectionWord_sub_centeredWord_le (W : Finset α)
    {r : ℕ} (hr : 0 < r) (hW : W.card = r) (position : Fin r → ι)
    (hposition : Function.Injective position) :
    ‖(∑ t : OrderedLabelTuple W r, M.projectionWord position t.val) -
        ∑ t : OrderedLabelTuple W r, M.centeredWord W position t‖ ≤
      scalarRestorationBound r (Fintype.card α) := by
  classical
  exact M.norm_sum_projectionWord_sub_centeredLabelWord_le hr position hposition
    univ (fun t : OrderedLabelTuple W r => t.val)
    (by rw [card_univ, card_full_orderedLabelTuple W hW])

/-- The crude centered-word estimate for a finite family also permits
repeated labels. Its size, rather than the number of distinct labels,
controls the sum. -/
theorem norm_sum_centeredLabelWord_le {τ : Type*} {r : ℕ}
    (position : Fin r → ι) (hposition : Function.Injective position)
    (T : Finset τ) (label : τ → Fin r → α) (hcard : T.card ≤ r.factorial) :
    ‖∑ t ∈ T, M.centeredLabelWord position (label t)‖ ≤
      (r.factorial : ℝ) * (2 * r + 1 : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
  let B : ℝ := (2 * r + 1 : ℝ) /
    Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ t ∈ T, ‖M.centeredLabelWord position (label t)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ T, B := sum_le_sum (fun t _ =>
      M.norm_centeredLabelWord_le position hposition (label t))
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (r.factorial : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
    _ = _ := by dsimp [B]; ring

/-- Combining the actual centered estimate and restoration gives the
repeated-label constant for any family of at most `r!` words. -/
theorem norm_sum_projectionWord_le_repeated_constant {τ : Type*} {r : ℕ}
    (hr : 0 < r) (position : Fin r → ι) (hposition : Function.Injective position)
    (T : Finset τ) (label : τ → Fin r → α) (hcard : T.card ≤ r.factorial) :
    ‖∑ t ∈ T, M.projectionWord position (label t)‖ ≤
      freeWordC r / Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
  have hd : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  apply repeated_freeWord_constant hd r
    (M.norm_sum_centeredLabelWord_le position hposition T label hcard)
    ((M.norm_sum_projectionWord_sub_centeredLabelWord_le hr position hposition T label hcard).trans
      (scalarRestorationBound_le hd r))
  calc
    _ = ‖(∑ t ∈ T, M.centeredLabelWord position (label t)) +
        ((∑ t ∈ T, M.projectionWord position (label t)) -
          ∑ t ∈ T, M.centeredLabelWord position (label t))‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

end FreeDiagonalModel

end

end KadisonKastler

end OAI
