import OAI.Combinatorics.Ryser.Construction.GadgetDefinitions
import OAI.Combinatorics.Ryser.Geometry.AffineJoins
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def originalLineSurvivors (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) :
    Finset (Point k) :=
  (linePoints (some d.val, z)).filter
    (fun p => ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e))

def originalLineCount (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) : ℝ :=
  (originalLineSurvivors a d z).card

@[simp] theorem mem_originalLineSurvivors (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (p : Point k) :
    p ∈ originalLineSurvivors a d z ↔
      Incidence p (some d.val, z) ∧
        ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e) := by
  simp only [originalLineSurvivors, Finset.mem_filter, mem_linePoints]

theorem originalLineSurvivors_eq_retained_filter (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineSurvivors a d z =
      (retainedPoints a).filter (fun p => Incidence p (some d.val, z)) := by
  ext p
  simp only [mem_originalLineSurvivors, Finset.mem_filter, mem_retainedPoints]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨?_, hp⟩
    intro e
    by_cases hed : e = d
    · subst e
      intro he
      change projection (some d.val) p = z at hp
      change projection (some d.val) p = a d at he
      exact hz (hp.symm.trans he)
    · exact havoid e hed
  · rintro ⟨havoid, hp⟩
    exact ⟨hp, fun e _ => havoid e⟩

theorem originalLineCount_eq_retained_filter_card (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineCount a d z =
      ((retainedPoints a).filter (fun p => Incidence p (some d.val, z))).card := by
  rw [originalLineCount, originalLineSurvivors_eq_retained_filter a d z hz]

theorem originalLineSurvivors_update_same (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z x : k) :
    originalLineSurvivors (Function.update a d x) d z = originalLineSurvivors a d z := by
  ext p
  simp only [mem_originalLineSurvivors]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed

private theorem originalLineSurvivors_card_le_add_one_of_agree_off
    (a b : GadgetOutcome k) (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k)
    (hid : i ≠ d) (hagree : ∀ e, e ≠ i → a e = b e) :
    (originalLineSurvivors a d z).card ≤ (originalLineSurvivors b d z).card + 1 := by
  have hlines : (some d.val, z) ≠ omittedLine b i := by
    intro h
    apply hid
    apply Subtype.ext
    exact (Option.some.inj (congrArg Prod.fst h)).symm
  have hinter :
      (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.mp hq
    exact eq_of_common_incidence_of_ne_lines hlines
      ((mem_linePoints _ _).mp hp₁) ((mem_linePoints _ _).mp hp₂)
      ((mem_linePoints _ _).mp hq₁) ((mem_linePoints _ _).mp hq₂)
  have hsub : originalLineSurvivors a d z ⊆
      originalLineSurvivors b d z ∪
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)) := by
    intro p hp
    by_cases hb : p ∈ originalLineSurvivors b d z
    · exact Finset.mem_union_left _ hb
    · apply Finset.mem_union_right
      have hp' := (mem_originalLineSurvivors a d z p).mp hp
      refine Finset.mem_inter.mpr ⟨(mem_linePoints _ _).mpr hp'.1, ?_⟩
      apply (mem_linePoints _ _).mpr
      by_contra hnot
      apply hb
      apply (mem_originalLineSurvivors b d z p).mpr
      refine ⟨hp'.1, ?_⟩
      intro e hed
      by_cases hei : e = i
      · subst e
        exact hnot
      · change ¬ Incidence p (some e.val, b e)
        rw [← hagree e hei]
        exact hp'.2 e hed
  calc
    (originalLineSurvivors a d z).card ≤
        (originalLineSurvivors b d z ∪
          (linePoints (some d.val, z) ∩ linePoints (omittedLine b i))).card :=
      Finset.card_le_card hsub
    _ ≤ (originalLineSurvivors b d z).card +
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card :=
      Finset.card_union_le _ _
    _ ≤ (originalLineSurvivors b d z).card + 1 := Nat.add_le_add_left hinter _

theorem originalLineCount_update_abs_le (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k) (x : k) :
    |originalLineCount (Function.update a i x) d z - originalLineCount a d z| ≤ 2 := by
  by_cases hid : i = d
  · subst i
    simp only [originalLineCount, originalLineSurvivors_update_same, sub_self, abs_zero]
    norm_num
  · have hforward := originalLineSurvivors_card_le_add_one_of_agree_off
      (Function.update a i x) a d z i hid (by
        intro e hei
        exact Function.update_of_ne hei x a)
    have hreverse := originalLineSurvivors_card_le_add_one_of_agree_off
      a (Function.update a i x) d z i hid (by
        intro e hei
        exact (Function.update_of_ne hei x a).symm)
    have hforwardR : originalLineCount (Function.update a i x) d z ≤
        originalLineCount a d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hforward
    have hreverseR : originalLineCount a d z ≤
        originalLineCount (Function.update a i x) d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hreverse
    apply abs_le.mpr
    constructor <;> linarith

end RyserCoveringCounterexample.Construction

end

end OAI
