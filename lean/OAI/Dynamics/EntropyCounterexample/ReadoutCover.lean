import Mathlib

namespace OAI

noncomputable section
namespace Problem340

def readoutCenter (i : Fin 3) : ℝ := 76 + (i : ℝ) / 2

def readoutBump (i : Fin 3) : ContDiffBump (readoutCenter i) :=
  ⟨1 / 4, 2 / 5, by norm_num, by norm_num⟩

def readoutCoeff (i : Fin 3) (t : ℝ) : ℝ := readoutBump i t

def readoutInterval (i : Fin 3) : Set ℝ :=
  Set.Ioo (readoutCenter i - 2 / 5) (readoutCenter i + 2 / 5)

theorem readoutCoeff_contDiff (i : Fin 3) {n : ℕ∞} :
    ContDiff ℝ n (readoutCoeff i) := (readoutBump i).contDiff

theorem readoutCoeff_nonneg (i : Fin 3) (t : ℝ) : 0 ≤ readoutCoeff i t :=
  (readoutBump i).nonneg

theorem readoutCoeff_le_one (i : Fin 3) (t : ℝ) : readoutCoeff i t ≤ 1 :=
  (readoutBump i).le_one

theorem readoutCoeff_support (i : Fin 3) :
    Function.support (readoutCoeff i) = readoutInterval i := by
  change Function.support (readoutBump i) = _
  rw [(readoutBump i).support_eq]
  ext t
  simp only [Metric.mem_ball, Real.dist_eq, readoutBump, readoutInterval,
    Set.mem_Ioo, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem readoutInterval_length (i : Fin 3) :
    (readoutCenter i + 2 / 5) - (readoutCenter i - 2 / 5) < 1 := by linarith

theorem readoutCenter_bounds (i : Fin 3) :
    76 ≤ readoutCenter i ∧ readoutCenter i ≤ 77 := by
  have hi : (i : ℕ) ≤ 2 := by omega
  have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  dsimp [readoutCenter]
  constructor <;> linarith

theorem readoutInterval_subset (i : Fin 3) :
    readoutInterval i ⊆ Set.Ioo 74 80 := by
  intro t ht
  obtain ⟨hc0, hc1⟩ := readoutCenter_bounds i
  change readoutCenter i - 2 / 5 < t ∧ t < readoutCenter i + 2 / 5 at ht
  constructor <;> linarith [ht.1, ht.2]

theorem readoutCoeff_eq_one (i : Fin 3) {t : ℝ}
    (ht : |t - readoutCenter i| ≤ 1 / 4) : readoutCoeff i t = 1 := by
  apply (readoutBump i).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, readoutBump] using ht

theorem readoutCoeff_cover {t : ℝ} (ht : t ∈ Set.Icc 76 77) :
    ∃ i : Fin 3, readoutCoeff i t = 1 := by
  rcases ht with ⟨ht0, ht1⟩
  by_cases h0 : t ≤ 76 + 1 / 4
  · refine ⟨0, readoutCoeff_eq_one 0 ?_⟩
    norm_num [readoutCenter, abs_le]
    constructor <;> linarith
  · by_cases h1 : t ≤ 76 + 3 / 4
    · refine ⟨1, readoutCoeff_eq_one 1 ?_⟩
      norm_num [readoutCenter, abs_le]
      constructor <;> linarith
    · refine ⟨2, readoutCoeff_eq_one 2 ?_⟩
      norm_num [readoutCenter, abs_le]
      constructor <;> linarith

def preparationBump : ContDiffBump (10 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def preparationCoeff (t : ℝ) : ℝ := preparationBump t

theorem preparationCoeff_contDiff {n : ℕ∞} : ContDiff ℝ n preparationCoeff :=
  preparationBump.contDiff

theorem preparationCoeff_nonneg (t : ℝ) : 0 ≤ preparationCoeff t :=
  preparationBump.nonneg

theorem preparationCoeff_le_one (t : ℝ) : preparationCoeff t ≤ 1 :=
  preparationBump.le_one

theorem preparationCoeff_support :
    Function.support preparationCoeff = Set.Ioo 8 12 := by
  change Function.support preparationBump = _
  rw [preparationBump.support_eq]
  ext t
  simp only [Metric.mem_ball, Real.dist_eq, preparationBump, Set.mem_Ioo, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem preparationCoeff_eq_one {t : ℝ} (ht : t ∈ Set.Icc 9 11) :
    preparationCoeff t = 1 := by
  apply preparationBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, Real.dist_eq, preparationBump, abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem readoutCoeff_hasCompactSupport (i : Fin 3) :
    HasCompactSupport (readoutCoeff i) := (readoutBump i).hasCompactSupport

theorem preparationCoeff_hasCompactSupport : HasCompactSupport preparationCoeff :=
  preparationBump.hasCompactSupport

theorem readoutCoeff_tsupport_subset (i : Fin 3) :
    tsupport (readoutCoeff i) ⊆
      Set.Ioo (readoutCenter i - 9 / 20) (readoutCenter i + 9 / 20) := by
  change tsupport (readoutBump i) ⊆ _
  rw [(readoutBump i).tsupport_eq]
  intro t ht
  have hh : |t - readoutCenter i| ≤ (2 : ℝ) / 5 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, readoutBump] using ht
  obtain ⟨hl, hr⟩ := abs_le.mp hh
  constructor <;> linarith

theorem readoutCoeff_closed_support_interval (i : Fin 3) :
    74 < readoutCenter i - 9 / 20 ∧ readoutCenter i + 9 / 20 < 80 ∧
    (readoutCenter i + 9 / 20) - (readoutCenter i - 9 / 20) < 1 := by
  obtain ⟨hl, hr⟩ := readoutCenter_bounds i
  constructor
  · linarith
  constructor <;> linarith

theorem exists_readoutCoeff_fderiv_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i : Fin 3, ∀ t : ℝ, ‖fderiv ℝ (readoutCoeff i) t‖ ≤ C := by
  have hlocal : ∀ i : Fin 3, ∃ C : ℝ, ∀ t : ℝ, ‖fderiv ℝ (readoutCoeff i) t‖ ≤ C := by
    intro i
    exact ((readoutCoeff_hasCompactSupport i).fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      ((readoutCoeff_contDiff i (n := 1)).continuous_fderiv (by norm_num))
  choose C hC using hlocal
  refine ⟨1 + ∑ i : Fin 3, |C i|, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i : Fin 3, |C i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  · intro i t
    have hi : |C i| ≤ ∑ j : Fin 3, |C j| :=
      Finset.single_le_sum (f := fun j : Fin 3 => |C j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (hC i t).trans ((le_abs_self (C i)).trans (by linarith))

theorem exists_preparationCoeff_fderiv_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, ‖fderiv ℝ preparationCoeff t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (preparationCoeff_hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((preparationCoeff_contDiff (n := 1)).continuous_fderiv (by norm_num))
  refine ⟨1 + |C|, le_add_of_nonneg_right (abs_nonneg C), fun t => ?_⟩
  exact (hC t).trans ((le_abs_self C).trans (by linarith))

end Problem340

end

end OAI
