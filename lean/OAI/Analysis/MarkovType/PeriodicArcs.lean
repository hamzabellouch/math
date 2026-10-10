import OAI.Analysis.MarkovType.FourLetters
import OAI.Analysis.MarkovType.PeriodicOrderIso
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def periodicIco (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j ≤ x ∧ x < b + j}

def periodicIcc (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j ≤ x ∧ x ≤ b + j}

def periodicIoo (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j < x ∧ x < b + j}

theorem mem_periodicIco_iff (a b x : ℝ) (hba : b < a + 1) :
    x ∈ periodicIco a b ↔ Int.fract (x - a) < b - a := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract]
    rw [hf]
    linarith
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · have hf := Int.floor_le (x - a)
      linarith
    · dsimp only [Int.fract] at h
      linarith

theorem mem_periodicIcc_iff (a b x : ℝ) (hba : b < a + 1) :
    x ∈ periodicIcc a b ↔ Int.fract (x - a) ≤ b - a := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract]
    rw [hf]
    linarith
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · have hf := Int.floor_le (x - a)
      linarith
    · dsimp only [Int.fract] at h
      linarith

theorem not_mem_periodicIco_iff (a b x : ℝ) (hab : a < b) (hba : b < a + 1) :
    x ∉ periodicIco a b ↔ ∃ j : ℤ, b + j ≤ x ∧ x < a + j + 1 := by
  rw [mem_periodicIco_iff a b x hba]
  constructor
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · dsimp only [Int.fract] at h
      linarith
    · have hf := Int.lt_floor_add_one (x - a)
      linarith
  · rintro ⟨j, hj0, hj1⟩ h
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract] at h
    rw [hf] at h
    linarith

theorem not_mem_periodicIcc_iff (a b x : ℝ) (hab : a < b) (hba : b < a + 1) :
    x ∉ periodicIcc a b ↔ ∃ j : ℤ, b + j < x ∧ x < a + j + 1 := by
  rw [mem_periodicIcc_iff a b x hba]
  constructor
  · intro h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · dsimp only [Int.fract] at h
      linarith
    · have hf := Int.lt_floor_add_one (x - a)
      linarith
  · rintro ⟨j, hj0, hj1⟩ h
    have hf : ⌊x - a⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    dsimp only [Int.fract] at h
    rw [hf] at h
    linarith

def arcRank (s : Letter) : ℕ := s.1.val + if s.2 then 0 else 2

def alpha (s : Letter) : ℝ := (2 * (arcRank s : ℝ) + 1) / 9

def beta (s : Letter) : ℝ := alpha s + 1 / 9

def arc (s : Letter) : Set ℝ := periodicIco (alpha s) (beta s)

def openArc (s : Letter) : Set ℝ := periodicIoo (alpha s) (beta s)

def closedArc (s : Letter) : Set ℝ := periodicIcc (alpha s) (beta s)

theorem alpha_pos (s : Letter) : 0 < alpha s := by
  rcases s with ⟨g, b⟩
  fin_cases g <;> cases b <;> norm_num [alpha, arcRank]

theorem alpha_lt_beta (s : Letter) : alpha s < beta s := by
  dsimp only [beta]
  linarith

theorem beta_lt_one (s : Letter) : beta s < 1 := by
  rcases s with ⟨g, b⟩
  fin_cases g <;> cases b <;> norm_num [beta, alpha, arcRank]

theorem beta_lt_alpha_add_one (s : Letter) : beta s < alpha s + 1 := by
  dsimp only [beta]
  linarith

theorem beta_lt_alpha_or (s t : Letter) (hne : s ≠ t) :
    beta s < alpha t ∨ beta t < alpha s := by
  rcases s with ⟨g, b⟩
  rcases t with ⟨g', b'⟩
  fin_cases g <;> fin_cases g' <;> cases b <;> cases b' <;>
    norm_num [beta, alpha, arcRank] at hne <;>
    norm_num [beta, alpha, arcRank]

theorem openArc_subset_arc (s : Letter) : openArc s ⊆ arc s := by
  rintro x ⟨j, hj0, hj1⟩
  exact ⟨j, hj0.le, hj1⟩

theorem arc_subset_closedArc (s : Letter) : arc s ⊆ closedArc s := by
  rintro x ⟨j, hj0, hj1⟩
  exact ⟨j, hj0, hj1.le⟩

theorem closedArc_fract {s : Letter} {x : ℝ} (hx : x ∈ closedArc s) :
    alpha s ≤ Int.fract x ∧ Int.fract x ≤ beta s := by
  obtain ⟨j, hj0, hj1⟩ := hx
  have hf : ⌊x⌋ = j := by
    apply Int.floor_eq_iff.mpr
    constructor
    · linarith [alpha_pos s]
    · linarith [beta_lt_one s]
  dsimp only [Int.fract]
  rw [hf]
  constructor <;> linarith

theorem not_mem_closedArc_int (s : Letter) (j : ℤ) : (j : ℝ) ∉ closedArc s := by
  intro h
  have h0 := (closedArc_fract h).1
  rw [Int.fract_intCast] at h0
  linarith [alpha_pos s]

theorem not_mem_arc_int (s : Letter) (j : ℤ) : (j : ℝ) ∉ arc s := by
  intro h
  exact not_mem_closedArc_int s j (arc_subset_closedArc s h)

theorem disjoint_closedArc (s t : Letter) (hne : s ≠ t) :
    Disjoint (closedArc s) (closedArc t) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hs := closedArc_fract hx
  have ht := closedArc_fract hy
  rcases beta_lt_alpha_or s t hne with h | h <;> linarith

theorem disjoint_arc {s t : Letter} (hne : s ≠ t) : Disjoint (arc s) (arc t) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (disjoint_closedArc s t hne)
    (arc_subset_closedArc s hx) (arc_subset_closedArc t hy)

theorem mem_arc_add_int_iff (s : Letter) (x : ℝ) (j : ℤ) :
    x + j ∈ arc s ↔ x ∈ arc s := by
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k - j, ?_, ?_⟩ <;> simp only [Int.cast_sub] <;> linarith
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k + j, ?_, ?_⟩ <;> simp only [Int.cast_add] <;> linarith

theorem mem_openArc_add_int_iff (s : Letter) (x : ℝ) (j : ℤ) :
    x + j ∈ openArc s ↔ x ∈ openArc s := by
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k - j, ?_, ?_⟩ <;> simp only [Int.cast_sub] <;> linarith
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k + j, ?_, ?_⟩ <;> simp only [Int.cast_add] <;> linarith

theorem isOpen_openArc (s : Letter) : IsOpen (openArc s) := by
  have he : openArc s = ⋃ j : ℤ, Set.Ioo (alpha s + j) (beta s + j) := by
    ext x
    simp only [openArc, periodicIoo, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioo]
  rw [he]
  exact isOpen_iUnion (fun _ => isOpen_Ioo)

theorem openArc_subset_interior_arc (s : Letter) : openArc s ⊆ interior (arc s) :=
  interior_maximal (openArc_subset_arc s) (isOpen_openArc s)

def positiveOrderIso (g : Fin 2) : ℝ ≃o ℝ :=
  translatedPeriodicOrderIso (alpha (g, false)) (beta (g, true) - 1)

def letterOrderIso (s : Letter) : ℝ ≃o ℝ :=
  if s.2 then positiveOrderIso s.1 else (positiveOrderIso s.1).symm

def letterHomeomorph (s : Letter) : ℝ ≃ₜ ℝ := (letterOrderIso s).toHomeomorph

@[simp] theorem letterHomeomorph_apply (s : Letter) (x : ℝ) :
    letterHomeomorph s x = letterOrderIso s x := rfl

theorem letterOrderIso_inv (s : Letter) : letterOrderIso s.inv = (letterOrderIso s).symm := by
  rcases s with ⟨g, b⟩
  cases b <;> rfl

theorem letterOrderIso_add_int (s : Letter) (x : ℝ) (j : ℤ) :
    letterOrderIso s (x + j) = letterOrderIso s x + j := by
  rcases s with ⟨g, b⟩
  cases b
  · exact translatedPeriodicOrderIso_symm_add_int _ _ x j
  · exact translatedPeriodicOrderIso_add_int _ _ x j

theorem positiveOrderIso_start (g : Fin 2) :
    positiveOrderIso g (alpha (g, false)) = beta (g, true) - 1 :=
  translatedPeriodicOrderIso_start _ _

theorem positiveOrderIso_break (g : Fin 2) :
    positiveOrderIso g (beta (g, false)) = alpha (g, true) := by
  change translatedPeriodicOrderIso (alpha (g, false)) (beta (g, true) - 1)
    (alpha (g, false) + 1 / 9) = alpha (g, true)
  rw [translatedPeriodicOrderIso_break]
  dsimp only [beta]
  ring

theorem positiveOrderIso_end (g : Fin 2) :
    positiveOrderIso g (alpha (g, false) + 1) = beta (g, true) := by
  unfold positiveOrderIso
  rw [translatedPeriodicOrderIso_end]
  ring

def letterPeriodShift (s : Letter) : ℤ := if s.2 then 0 else 1

theorem letterOrderIso_beta_inv_base (s : Letter) :
    letterOrderIso s (beta s.inv) = alpha s + (letterPeriodShift s : ℤ) := by
  rcases s with ⟨g, b⟩
  cases b
  · rw [show letterPeriodShift (g, false) = (1 : ℤ) from rfl, Int.cast_one]
    change (positiveOrderIso g).symm (beta (g, true)) = alpha (g, false) + 1
    apply (positiveOrderIso g).injective
    rw [(positiveOrderIso g).apply_symm_apply, positiveOrderIso_end]
  · rw [show letterPeriodShift (g, true) = (0 : ℤ) from rfl, Int.cast_zero]
    change positiveOrderIso g (beta (g, false)) = alpha (g, true) + 0
    simpa only [add_zero] using positiveOrderIso_break g

theorem letterOrderIso_alpha_inv_add_one_base (s : Letter) :
    letterOrderIso s (alpha s.inv + 1) = beta s + (letterPeriodShift s : ℤ) := by
  rcases s with ⟨g, b⟩
  cases b
  · rw [show letterPeriodShift (g, false) = (1 : ℤ) from rfl, Int.cast_one]
    change (positiveOrderIso g).symm (alpha (g, true) + 1) = beta (g, false) + 1
    apply (positiveOrderIso g).injective
    rw [(positiveOrderIso g).apply_symm_apply]
    have h := letterOrderIso_add_int (g, true) (beta (g, false)) (1 : ℤ)
    rw [Int.cast_one] at h
    change positiveOrderIso g (beta (g, false) + 1) =
      positiveOrderIso g (beta (g, false)) + 1 at h
    rw [positiveOrderIso_break] at h
    exact h.symm
  · rw [show letterPeriodShift (g, true) = (0 : ℤ) from rfl, Int.cast_zero]
    change positiveOrderIso g (alpha (g, false) + 1) = beta (g, true) + 0
    simpa only [add_zero] using positiveOrderIso_end g

theorem letterOrderIso_beta_inv (s : Letter) (j : ℤ) :
    letterOrderIso s (beta s.inv + j) = alpha s + ((j + letterPeriodShift s : ℤ) : ℝ) := by
  rw [letterOrderIso_add_int, letterOrderIso_beta_inv_base]
  simp only [Int.cast_add]
  ring

theorem letterOrderIso_alpha_inv_add_one (s : Letter) (j : ℤ) :
    letterOrderIso s (alpha s.inv + j + 1) = beta s + ((j + letterPeriodShift s : ℤ) : ℝ) := by
  rw [show alpha s.inv + (j : ℝ) + 1 = (alpha s.inv + 1) + j by ring,
    letterOrderIso_add_int, letterOrderIso_alpha_inv_add_one_base]
  simp only [Int.cast_add]
  ring

theorem mem_arc_iff_not_mem_inv_arc (s : Letter) (x : ℝ) :
    letterOrderIso s x ∈ arc s ↔ x ∉ arc s.inv := by
  change letterOrderIso s x ∈ periodicIco (alpha s) (beta s) ↔
    x ∉ periodicIco (alpha s.inv) (beta s.inv)
  rw [not_mem_periodicIco_iff _ _ x (alpha_lt_beta s.inv)
    (beta_lt_alpha_add_one s.inv)]
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k - letterPeriodShift s, ?_, ?_⟩
    · apply (letterOrderIso s).le_iff_le.mp
      rw [letterOrderIso_beta_inv]
      simpa only [sub_add_cancel] using hk0
    · apply (letterOrderIso s).lt_iff_lt.mp
      rw [letterOrderIso_alpha_inv_add_one]
      simpa only [sub_add_cancel] using hk1
  · rintro ⟨j, hj0, hj1⟩
    refine ⟨j + letterPeriodShift s, ?_, ?_⟩
    · simpa only [letterOrderIso_beta_inv] using (letterOrderIso s).monotone hj0
    · simpa only [letterOrderIso_alpha_inv_add_one] using (letterOrderIso s).strictMono hj1

theorem image_compl_arc (s : Letter) : letterOrderIso s '' (arc s.inv)ᶜ = arc s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_arc_iff_not_mem_inv_arc s x).mpr hx
  · intro hy
    refine ⟨(letterOrderIso s).symm y, ?_, (letterOrderIso s).apply_symm_apply y⟩
    apply (mem_arc_iff_not_mem_inv_arc s _).mp
    simpa only [(letterOrderIso s).apply_symm_apply] using hy

theorem symm_mem_inv_arc_iff (s : Letter) (y : ℝ) :
    (letterOrderIso s).symm y ∈ arc s.inv ↔ y ∉ arc s := by
  have h := mem_arc_iff_not_mem_inv_arc s ((letterOrderIso s).symm y)
  rw [(letterOrderIso s).apply_symm_apply] at h
  constructor
  · intro hx hy
    exact (h.mp hy) hx
  · intro hy
    by_contra hx
    exact hy (h.mpr hx)

theorem map_mem_openArc_of_not_mem_closedArc (s : Letter) {x : ℝ}
    (hx : x ∉ closedArc s.inv) : letterOrderIso s x ∈ openArc s := by
  obtain ⟨j, hj0, hj1⟩ := (not_mem_periodicIcc_iff _ _ x (alpha_lt_beta s.inv)
    (beta_lt_alpha_add_one s.inv)).mp hx
  refine ⟨j + letterPeriodShift s, ?_, ?_⟩
  · simpa only [letterOrderIso_beta_inv] using (letterOrderIso s).strictMono hj0
  · simpa only [letterOrderIso_alpha_inv_add_one] using (letterOrderIso s).strictMono hj1

theorem letterOrderIso_zero_mem_openArc (s : Letter) : letterOrderIso s 0 ∈ openArc s := by
  apply map_mem_openArc_of_not_mem_closedArc
  simpa only [Int.cast_zero] using not_mem_closedArc_int s.inv 0

theorem letterOrderIso_mem_openArc_of_mem_openArc (s t : Letter) (hne : t ≠ s.inv)
    {x : ℝ} (hx : x ∈ openArc t) : letterOrderIso s x ∈ openArc s := by
  apply map_mem_openArc_of_not_mem_closedArc
  intro hs
  exact Set.disjoint_left.mp (disjoint_closedArc t s.inv hne)
    (arc_subset_closedArc t (openArc_subset_arc t hx)) hs

theorem positiveOrderIso_displacement (g : Fin 2) (x : ℝ) :
    -(4 / 3 : ℝ) ≤ positiveOrderIso g x - x ∧
      positiveOrderIso g x - x ≤ -(5 / 9 : ℝ) := by
  have h := translatedPeriodicOrderIso_displacement (alpha (g, false))
    (beta (g, true) - 1) x
  change beta (g, true) - 1 - alpha (g, false) ≤ positiveOrderIso g x - x ∧
    positiveOrderIso g x - x ≤ beta (g, true) - 1 - alpha (g, false) + 7 / 9 at h
  have hc : beta (g, true) - 1 - alpha (g, false) = -(4 / 3 : ℝ) := by
    fin_cases g <;> norm_num [beta, alpha, arcRank]
  rw [hc] at h
  change -(4 / 3 : ℝ) ≤ positiveOrderIso g x - x ∧
    positiveOrderIso g x - x ≤ -(5 / 9 : ℝ)
  constructor <;> linarith

theorem letterOrderIso_abs_move_le (s : Letter) (x : ℝ) :
    |letterOrderIso s x - x| ≤ (4 / 3 : ℝ) := by
  rcases s with ⟨g, b⟩
  cases b
  · change |(positiveOrderIso g).symm x - x| ≤ (4 / 3 : ℝ)
    have h := positiveOrderIso_displacement g ((positiveOrderIso g).symm x)
    rw [(positiveOrderIso g).apply_symm_apply] at h
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |positiveOrderIso g x - x| ≤ (4 / 3 : ℝ)
    have h := positiveOrderIso_displacement g x
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem letterOrderIso_displacement_lt (s : Letter) (x : ℝ) :
    |letterOrderIso s x - x| < 2 :=
  lt_of_le_of_lt (letterOrderIso_abs_move_le s x) (by norm_num)

end MarkovSuperreflexivity

end

end OAI
