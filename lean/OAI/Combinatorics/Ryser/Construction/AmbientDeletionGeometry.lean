import OAI.Combinatorics.Ryser.Construction.DeletionLines
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import OAI.Combinatorics.Ryser.Selection.Forbidden

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def shiftAffineLine (b : Point F) (l : AffineLine F) : AffineLine F :=
  (l.1, l.2 + projection l.1 b)

@[simp] theorem shiftAffineLine_direction (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).1 = l.1 := rfl

@[simp] theorem shiftAffineLine_offset (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).2 = l.2 + projection l.1 b := rfl

@[simp] theorem shiftAffineLine_zero (l : AffineLine F) : shiftAffineLine 0 l = l := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [shiftAffineLine, projection]

theorem shiftAffineLine_injective (b : Point F) : Function.Injective (shiftAffineLine b) := by
  intro l m h
  have hdir := congrArg Prod.fst h
  change l.1 = m.1 at hdir
  apply Prod.ext hdir
  have hoff := congrArg Prod.snd h
  change l.2 + projection l.1 b = m.2 + projection m.1 b at hoff
  rw [hdir] at hoff
  exact add_right_cancel hoff

theorem incidence_shiftAffineLine_iff (b x : Point F) (l : AffineLine F) :
    Incidence x (shiftAffineLine b l) ↔ Incidence (x - b) l := by
  change projection l.1 x = l.2 + projection l.1 b ↔ projection l.1 (x - b) = l.2
  have hproj : projection l.1 (x - b) = projection l.1 x - projection l.1 b :=
    projection_sub l.1 x b
  rw [hproj, sub_eq_iff_eq_add]

section Finite

variable [Fintype F] [DecidableEq F]

def ambientLineUnion (B : Finset (AffineLine F)) : Finset (Point F) :=
  B.biUnion linePoints

@[simp] theorem mem_ambientLineUnion (B : Finset (AffineLine F)) (x : Point F) :
    x ∈ ambientLineUnion B ↔ ∃ l ∈ B, Incidence x l := by
  simp only [ambientLineUnion, Finset.mem_biUnion, mem_linePoints]

theorem mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (b x : Point F) :
    x ∈ ambientLineUnion (B.image (shiftAffineLine b)) ↔ x - b ∈ ambientLineUnion B := by
  rw [mem_ambientLineUnion, mem_ambientLineUnion]
  constructor
  · rintro ⟨l, hl, hxl⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨m, hm, (incidence_shiftAffineLine_iff b x m).mp hxl⟩
  · rintro ⟨l, hl, hxl⟩
    exact ⟨shiftAffineLine b l, Finset.mem_image.mpr ⟨l, hl, rfl⟩,
      (incidence_shiftAffineLine_iff b x l).mpr hxl⟩

theorem card_ambientLineUnion_le (B : Finset (AffineLine F)) :
    (ambientLineUnion B).card ≤ B.card * Fintype.card F :=
  Finset.card_biUnion_le_card_mul B linePoints (Fintype.card F)
    (fun l _ => (card_linePoints l).le)

theorem uniform_prob_mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) =
      ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  have hinj : Function.Injective (fun y : Point F => x - y) := by
    intro y z hyz
    have h := congrArg (fun w : Point F => x - w) hyz
    simpa only [sub_sub_cancel] using h
  rw [FiniteLaw.uniform_prob]
  calc
    _ = (((ambientLineUnion B).image (fun y => x - y)).card : ℝ) /
        (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_ambientLineUnion_shift]
      constructor
      · intro hb
        exact Finset.mem_image.mpr ⟨x - b, hb, sub_sub_cancel x b⟩
      · intro hb
        obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
        rw [← hyb, sub_sub_cancel]
        exact hy
    _ = _ := by
      rw [Finset.card_image_of_injective _ hinj, card_point, Nat.cast_pow]

theorem uniform_prob_mem_ambientLineUnion_shift_le (B : Finset (AffineLine F))
    (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) ≤
      (B.card : ℝ) / (Fintype.card F : ℝ) := by
  rw [uniform_prob_mem_ambientLineUnion_shift]
  have hcard : ((ambientLineUnion B).card : ℝ) ≤
      (B.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast card_ambientLineUnion_le B
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤
        ((B.card : ℝ) * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = (B.card : ℝ) / (Fintype.card F : ℝ) := by
      field_simp [hq]

theorem uniform_prob_mem_image_shiftAffineLine_le (B : Finset (AffineLine F))
    (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ B.image (shiftAffineLine b)) ≤
      ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
  classical
  let T := B.filter (fun e => e.1 = l.1)
  have hP : (fun b => l ∈ B.image (shiftAffineLine b)) =
      (fun b => ∃ e : ↥T, projection l.1 b = l.2 - e.val.2) := by
    funext b
    apply propext
    constructor
    · intro hb
      obtain ⟨e, heB, heq⟩ := Finset.mem_image.mp hb
      have hdir := congrArg Prod.fst heq
      change e.1 = l.1 at hdir
      have hoff := congrArg Prod.snd heq
      change e.2 + projection e.1 b = l.2 at hoff
      have hproj : projection l.1 b = l.2 - e.2 := by
        rw [← hdir]
        apply (eq_sub_iff_add_eq).2
        exact (add_comm _ _).trans hoff
      exact ⟨⟨e, Finset.mem_filter.mpr ⟨heB, hdir⟩⟩, hproj⟩
    · rintro ⟨e, heq⟩
      have hdir : e.val.1 = l.1 := (Finset.mem_filter.mp e.property).2
      refine Finset.mem_image.mpr ⟨e.val, (Finset.mem_filter.mp e.property).1, ?_⟩
      apply Prod.ext
      · exact hdir
      · change e.val.2 + projection e.val.1 b = l.2
        rw [hdir, heq]
        ring
  rw [hP]
  calc
    _ ≤ ∑ e : ↥T, (FiniteLaw.uniform (Point F)).prob
        (fun b => projection l.1 b = l.2 - e.val.2) := FiniteLaw.prob_exists_le _ _
    _ = ∑ _e : ↥T, 1 / (Fintype.card F : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact Selection.uniform_prob_projection l.1 (l.2 - e.val.2)
    _ = ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
      simp [T, div_eq_mul_inv]

end Finite

section Placed

variable {k : Type*} [Field k] [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k]
variable [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem placedPoint_sub_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (y : Point k) :
    placedPoint σ M b y - b = placedPoint σ M 0 y := let _ := instFintypek; let _ := instDecidableEqk; let _ := instFintypeF; let _ := instDecidableEqF; by
  simp only [placedPoint, add_sub_cancel_left, zero_add]

theorem mem_deletedLines_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (l : AffineLine F) :
    shiftAffineLine b l ∈ deletedLines σ M b a ↔ l ∈ deletedLines σ M 0 a := by
  simp only [mem_deletedLines, shiftAffineLine_direction, incidence_shiftAffineLine_iff,
    placedPoint_sub_shift]

theorem deletedLines_eq_image_shiftAffineLine (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) :
    deletedLines σ M b a = (deletedLines σ M 0 a).image (shiftAffineLine b) := by
  ext l
  constructor
  · intro hl
    let m : AffineLine F := (l.1, l.2 - projection l.1 b)
    have hm : shiftAffineLine b m = l := by
      apply Prod.ext
      · rfl
      · exact sub_add_cancel _ _
    refine Finset.mem_image.mpr ⟨m, ?_, hm⟩
    apply (mem_deletedLines_shift σ M b a m).mp
    rw [hm]
    exact hl
  · intro hl
    obtain ⟨m, hm, hml⟩ := Finset.mem_image.mp hl
    rw [← hml]
    exact (mem_deletedLines_shift σ M b a m).mpr hm

theorem uniform_prob_mem_deletedLines_union (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_union_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) ≤
      ((deletedLines σ M 0 a).card : ℝ) / (Fintype.card F : ℝ) := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift_le (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ deletedLines σ M b a) ≤
      (((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)).card : ℝ) /
        (Fintype.card F : ℝ) := by
  have hP : (fun b => l ∈ deletedLines σ M b a) =
      (fun b => l ∈ (deletedLines σ M 0 a).image (shiftAffineLine b)) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_image_shiftAffineLine_le (deletedLines σ M 0 a) l

end Placed

end RyserCoveringCounterexample.Construction

end

end OAI
