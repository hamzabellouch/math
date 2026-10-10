import OAI.Probability.InvariantIsing.Cavity.CavityFiniteDeficitPath

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

def cavityInteriorLevel {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  ((i : ℕ) + 1 : ℝ) / (n + 2 : ℕ)

lemma cavityInteriorLevel_mem {n : ℕ} (i : Fin (n + 1)) :
    cavityInteriorLevel i ∈ Ioo (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hi : ((i : ℕ) + 1 : ℝ) < (n + 2 : ℕ) := by
    exact_mod_cast (show i.val + 1 < n + 2 by omega)
  exact ⟨div_pos (by positivity) hd, (div_lt_one hd).mpr hi⟩

lemma cavityInteriorLevel_strict (n : ℕ) :
    StrictMono (cavityInteriorLevel (n := n)) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < (n + 2 : ℕ) by positivity)).mpr
  simpa only [add_comm] using add_lt_add_right (Nat.cast_lt.mpr hij : (i.val : ℝ) < j.val) 1

def cavityStrictLevels {n : ℕ} (q : Fin (n + 1) → ℝ) (ε : ℝ)
    (i : Fin (n + 1)) : ℝ := (1 - ε) * q i + ε * cavityInteriorLevel i

lemma cavityStrictLevels_mem {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (i : Fin (n + 1)) : cavityStrictLevels q ε i ∈ Ioo (0 : ℝ) 1 := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hnon : 0 ≤ (1 - ε) * q i := mul_nonneg (sub_nonneg.mpr hε.2) hq'.1
  have hpos : 0 < ε * cavityInteriorLevel i := mul_pos hε.1 hi.1
  have hlo : (1 - ε) * q i ≤ (1 - ε) := by nlinarith [mul_nonneg (sub_nonneg.mpr hε.2) (sub_nonneg.mpr hq'.2)]
  have hhi : ε * cavityInteriorLevel i < ε := by nlinarith [mul_pos hε.1 (sub_pos.mpr hi.2)]
  constructor <;> dsimp only [cavityStrictLevels] <;> linarith

lemma cavityStrictLevels_strict {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : Monotone q) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    StrictMono (cavityStrictLevels q ε) := by
  intro i j hij
  have hq' := mul_le_mul_of_nonneg_left (hq hij.le) (sub_nonneg.mpr hε.2)
  have hi := mul_lt_mul_of_pos_left (cavityInteriorLevel_strict n hij) hε.1
  exact add_lt_add_of_le_of_lt hq' hi

lemma cavityStrictLevels_dist {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin (n + 1)) : |cavityStrictLevels q ε i - q i| ≤ ε := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hd : |cavityInteriorLevel i - q i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2, hq'.1, hq'.2]
  have he : cavityStrictLevels q ε i - q i = ε * (cavityInteriorLevel i - q i) := by
    dsimp only [cavityStrictLevels]
    ring
  rw [he, abs_mul, abs_of_nonneg hε]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hε

end InvariantIsing

end

end OAI
