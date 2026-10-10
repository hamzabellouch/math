import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem direction_eq_of_common_point (p r : Point F) (hne : p ≠ r)
    (d e : Direction F) (hd : OnLine r (lineThrough d p))
    (he : OnLine r (lineThrough e p)) : d = e := by
  have h := eq_of_two_common_points p r hne (lineThrough d p) (lineThrough e p)
    (onLine_lineThrough d p) hd (onLine_lineThrough e p) he
  exact congrArg Prod.fst h

variable [DecidableEq F]

theorem existsUnique_direction_of_ne (p r : Point F) (hne : p ≠ r) :
    ∃! d : Direction F, OnLine r (lineThrough d p) := by
  have hline : lineThrough (joiningLine p r).1 p = joiningLine p r :=
    (line_eq_lineThrough p (joiningLine p r) (onLine_joiningLine_left p r)).symm
  refine ⟨(joiningLine p r).1, ?_, ?_⟩
  · change OnLine r (lineThrough (joiningLine p r).1 p)
    rw [hline]
    exact onLine_joiningLine_right p r
  · intro d hd
    apply direction_eq_of_common_point p r hne d (joiningLine p r).1 hd
    rw [hline]
    exact onLine_joiningLine_right p r

variable [Fintype F]

theorem card_directions_to_point (p r : Point F) (hne : p ≠ r) :
    ((Finset.univ : Finset (Direction F)).filter
      (fun d => OnLine r (lineThrough d p))).card = 1 := by
  classical
  obtain ⟨d, hd, hu⟩ := existsUnique_direction_of_ne p r hne
  apply Finset.card_eq_one.mpr
  refine ⟨d, ?_⟩
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun he => hu e he, fun he => he ▸ hd⟩

theorem card_directions_meeting_pair_away_le_one
    (D : Finset (Direction F)) (p : Point F) (l m : Line F) (hne : l ≠ m) :
    (D.filter (fun d => ∃ x : Point F, x ≠ p ∧ OnLine x l ∧
      OnLine x m ∧ OnLine x (lineThrough d p))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro d hd e he
  obtain ⟨x, hxp, hxl, hxm, hxd⟩ := (Finset.mem_filter.mp hd).2
  obtain ⟨y, hyp, hyl, hym, hye⟩ := (Finset.mem_filter.mp he).2
  have hxy : x = y := common_point_eq_of_lines_ne l m hne x y hxl hxm hyl hym
  subst y
  exact direction_eq_of_common_point p x (Ne.symm hxp) d e hxd hye

theorem card_projection_directions_le_one
    (D : Finset (Direction F)) (p : Point F) (l m : Line F) (hne : l ≠ m) :
    (D.filter (fun d => d ≠ l.1 ∧
      lineIntersection l (lineThrough d p) ≠ p ∧
      OnLine (lineIntersection l (lineThrough d p)) m)).card ≤ 1 := by
  classical
  apply le_trans (Finset.card_le_card ?_)
    (card_directions_meeting_pair_away_le_one D p l m hne)
  intro d hd
  obtain ⟨hdD, hdir, haway, hm⟩ := Finset.mem_filter.mp hd
  refine Finset.mem_filter.mpr ⟨hdD, lineIntersection l (lineThrough d p),
    haway, ?_, hm, ?_⟩
  · exact onLine_lineIntersection_left l (lineThrough d p) (Ne.symm hdir)
  · exact onLine_lineIntersection_right l (lineThrough d p) (Ne.symm hdir)

theorem projection_direction_fraction_le
    (D : Finset (Direction F)) (p : Point F) (l m : Line F) (hne : l ≠ m) :
    (((D.filter (fun d => d ≠ l.1 ∧
      lineIntersection l (lineThrough d p) ≠ p ∧
      OnLine (lineIntersection l (lineThrough d p)) m)).card : ℝ) /
      (D.card : ℝ)) ≤ 1 / (D.card : ℝ) := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_projection_directions_le_one D p l m hne

theorem projection_uniform_probability_le
    (D : Finset (Direction F)) (hD : D.Nonempty)
    (p : Point F) (l m : Line F) (hne : l ≠ m) :
    ((PMF.uniformOfFinset D hD).toOuterMeasure
      {d | d ≠ l.1 ∧ lineIntersection l (lineThrough d p) ≠ p ∧
        OnLine (lineIntersection l (lineThrough d p)) m}).toReal ≤
      1 / (D.card : ℝ) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  exact projection_direction_fraction_le D p l m hne

theorem point_uniform_direction_probability (p r : Point F) (hne : p ≠ r) :
    ((PMF.uniformOfFintype (Direction F)).toOuterMeasure
      {d | OnLine r (lineThrough d p)}).toReal =
      1 / ((Fintype.card F : ℝ) + 1) := by
  classical
  rw [PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, card_directions_to_point p r hne,
    Finset.card_univ, Direction, Fintype.card_option]
  rw [ENNReal.toReal_div, Nat.cast_add, Nat.cast_one,
    ENNReal.toReal_add (by simp) (by simp)]
  simp

end Balanced

end OAI
