import OAI.Combinatorics.Ryser.Construction.CoverPencil
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import OAI.Combinatorics.Ryser.Probability.Finite
import Mathlib.Algebra.Group.Prod

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

def ShiftHits (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) : Prop :=
  ∃ w ∈ W, ∃ d ∈ S, Incidence (b + w) ell ∧
    projection d (b + w) = projection d p

def badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (ShiftHits W S p ell)

@[simp] theorem mem_badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) :
    b ∈ badShifts W S p ell ↔ ShiftHits W S p ell b := let _ := instDecidableEqF; by
  classical
  simp only [badShifts, Finset.mem_filter, Finset.mem_univ, true_and]

theorem badShifts_eq_biUnion (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) :
    badShifts W S p ell = W.biUnion (fun w => S.biUnion (fun d =>
      (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))) := by
  ext b
  constructor
  · intro hb
    obtain ⟨w, hw, d, hd, hbell, hbd⟩ := (mem_badShifts W S p ell b).mp hb
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hw, Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨b + w, Finset.mem_inter.mpr ⟨?_, ?_⟩, by simp⟩
    · exact (mem_linePoints _ _).mpr hbell
    · exact (mem_linePoints _ _).mpr hbd
  · intro hb
    obtain ⟨w, hw, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨d, hd, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
    apply (mem_badShifts W S p ell b).mpr
    have hby : b + w = y := by rw [← hyb]; simp
    refine ⟨w, hw, d, hd, ?_, ?_⟩
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2

theorem badShifts_card_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (badShifts W S p ell).card ≤ W.card * S.card := by
  have hpoint (d : Direction F) :
      (linePoints ell ∩ linePoints (lineThrough d p)).card ≤ 1 := by
    apply card_linePoints_inter_le_one
    intro heq
    exact hp (heq.symm ▸ incidence_lineThrough d p)
  rw [badShifts_eq_biUnion]
  calc
    _ ≤ ∑ w ∈ W, (S.biUnion (fun d =>
        (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ W, S.card := by
      apply Finset.sum_le_sum
      intro w hw
      calc
        _ ≤ ∑ d ∈ S,
            ((linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _d ∈ S, 1 := Finset.sum_le_sum fun d _ =>
          Finset.card_image_le.trans (hpoint d)
        _ = S.card := by simp
    _ = W.card * S.card := by simp

theorem uniform_prob_shiftHits_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Point F)).prob (ShiftHits W S p ell) ≤
      (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 := by
  classical
  rw [FiniteLaw.uniform_prob]
  change ((badShifts W S p ell).card : ℝ) / Fintype.card (Point F) ≤ _
  rw [card_point, Nat.cast_pow]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast badShifts_card_le W S p ell hp
  · positivity

end RyserCoveringCounterexample.Construction

end

end OAI
