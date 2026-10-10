import OAI.Geometry.CylinderCovering.Angular.OrdinaryCapsDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapArea

namespace OAI

open Set
namespace CylinderCovering.AngularOrdinaryCaps
open GeneralCapArea

lemma interval_abs_le {l r q : ℝ} (hl : |l| ≤ 1) (hr : |r| ≤ 1)
    (hq : q ∈ Icc l r) : |q| ≤ 1 :=
  abs_le.mpr ⟨(abs_le.mp hl).1.trans hq.1, hq.2.trans (abs_le.mp hr).2⟩

lemma profile_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |profile p - profile q| ≤ |p - q| := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hsum : |p + q| ≤ 2 := (abs_add_le _ _).trans (by linarith only [hp, hq])
  have hs0 : 0 ≤ 1 + p ^ 2 + q ^ 2 := by positivity
  have hs1 : 1 + p ^ 2 + q ^ 2 ≤ 3 := by linarith only [hp2, hq2]
  have hid : profile p - profile q =
      (p - q) * ((p + q) * (1 + p ^ 2 + q ^ 2) / 16) := by
    unfold profile
    ring
  rw [hid, abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [abs_div, abs_mul, abs_of_nonneg hs0]
  norm_num
  have hprod := mul_le_mul hsum hs1 hs0 (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [hprod]

lemma profile_le_max_endpoints {l r q : ℝ} (hq : q ∈ Icc l r) :
    profile q ≤ max (profile l) (profile r) := by
  have hsq : q ^ 2 ≤ max (l ^ 2) (r ^ 2) := by
    by_cases h0 : 0 ≤ q
    · have hr0 : 0 ≤ r := h0.trans hq.2
      exact ((sq_le_sq₀ h0 hr0).mpr hq.2).trans (le_max_right _ _)
    · have hq0 : q ≤ 0 := (lt_of_not_ge h0).le
      have hl0 : l ≤ 0 := hq.1.trans hq0
      have h : q ^ 2 ≤ l ^ 2 := by nlinarith only [hq.1, hq0, hl0]
      exact h.trans (le_max_left _ _)
  rcases le_max_iff.mp hsq with h | h
  · apply le_trans _ (le_max_left _ _)
    unfold profile
    have hp := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ l ^ 2 + q ^ 2 by positivity)
    nlinarith only [h, hp]
  · apply le_trans _ (le_max_right _ _)
    unfold profile
    have hp := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ r ^ 2 + q ^ 2 by positivity)
    nlinarith only [h, hp]

lemma maximumProfile_eq_sSup {l r : ℝ} (hlr : l ≤ r) :
    max (profile l) (profile r) = sSup (profile '' Icc l r) := by
  apply le_antisymm
  · apply max_le
    · apply le_csSup
      · exact ⟨max (profile l) (profile r), by
          rintro z ⟨q, hq, rfl⟩
          exact profile_le_max_endpoints hq⟩
      · exact ⟨l, ⟨le_rfl, hlr⟩, rfl⟩
    · apply le_csSup
      · exact ⟨max (profile l) (profile r), by
          rintro z ⟨q, hq, rfl⟩
          exact profile_le_max_endpoints hq⟩
      · exact ⟨r, ⟨hlr, le_rfl⟩, rfl⟩
  · apply csSup_le
    · exact ⟨profile l, l, ⟨le_rfl, hlr⟩, rfl⟩
    · rintro z ⟨q, hq, rfl⟩
      exact profile_le_max_endpoints hq

lemma shared_left (l r : ℝ) :
    secantAlpha l r - l * secantBeta l r = (1 - l ^ 2) / 4 := by
  unfold secantAlpha secantBeta
  ring

lemma shared_right (l r : ℝ) :
    secantAlpha l r - r * secantBeta l r = (1 - r ^ 2) / 4 := by
  unfold secantAlpha secantBeta
  ring

lemma secantBeta_error {l r q : ℝ} (hq : q ∈ Icc l r) :
    |secantBeta l r - q / 2| ≤ (r - l) / 4 := by
  rw [abs_le]
  unfold secantBeta
  constructor <;> linarith [hq.1, hq.2]

lemma secantAlpha_error {l r q : ℝ} (hl : |l| ≤ 1) (hr : |r| ≤ 1)
    (hq : q ∈ Icc l r) :
    |secantAlpha l r - (1 + q ^ 2) / 4| ≤ (r - l) / 2 := by
  have hqabs := interval_abs_le hl hr hq
  have hid : secantAlpha l r - (1 + q ^ 2) / 4 =
      (l * (r - q) + q * (l - q)) / 4 := by unfold secantAlpha; ring
  have h1 : |l * (r - q)| ≤ r - q := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hq.2)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hq.2) hl
  have h2 : |q * (l - q)| ≤ q - l := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hq.1)]
    nlinarith only [mul_le_of_le_one_left (sub_nonneg.mpr hq.1) hqabs]
  rw [hid, abs_div]
  norm_num
  have h := abs_add_le (l * (r - q)) (q * (l - q))
  linarith only [h, h1, h2, hq.1, hq.2]

lemma profile_cell_error {l r p q : ℝ} (hl : |l| ≤ 1) (hr : |r| ≤ 1)
    (hp : p ∈ Icc l r) (hq : q ∈ Icc l r) :
    |profile p - profile q| ≤ r - l := by
  have h := profile_lipschitz (interval_abs_le hl hr hp) (interval_abs_le hl hr hq)
  have hd : |p - q| ≤ r - l := by
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  exact h.trans hd

lemma max_profile_cell_error {l r q : ℝ} (hl : |l| ≤ 1) (hr : |r| ≤ 1)
    (hq : q ∈ Icc l r) :
    |max (profile l) (profile r) - profile q| ≤ r - l := by
  have hlr : l ≤ r := hq.1.trans hq.2
  have h1 := profile_cell_error hl hr (show l ∈ Icc l r from ⟨le_rfl, hlr⟩) hq
  have h2 := profile_cell_error hl hr (show r ∈ Icc l r from ⟨hlr, le_rfl⟩) hq
  rw [abs_le]
  constructor
  · have h := profile_le_max_endpoints hq
    linarith only [h, hlr]
  · exact sub_le_iff_le_add.mpr (max_le (by linarith [(abs_le.mp h1).2])
      (by linarith [(abs_le.mp h2).2]))

lemma taggedRadius_error {ε η M l r t q : ℝ}
    (hl : |l| ≤ 1) (hr : |r| ≤ 1) (ht : t ∈ Icc l r) (hq : q ∈ Icc l r)
    (hmesh : r - l ≤ M * ε ^ 2) :
    |taggedRadius ε η t - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ M * ε ^ 4 := by
  have hp := profile_cell_error hl hr ht hq
  have hid : taggedRadius ε η t - (1 / 2 + ε ^ 2 * (profile q + η)) =
      ε ^ 2 * (profile t - profile q) := by unfold taggedRadius; ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg ε)]
  calc
    _ ≤ ε ^ 2 * (r - l) := mul_le_mul_of_nonneg_left hp (sq_nonneg ε)
    _ ≤ ε ^ 2 * (M * ε ^ 2) := mul_le_mul_of_nonneg_left hmesh (sq_nonneg ε)
    _ = _ := by ring

lemma midpointRadius_error {ε η M l r q : ℝ}
    (hl : |l| ≤ 1) (hr : |r| ≤ 1) (hq : q ∈ Icc l r)
    (hmesh : r - l ≤ M * ε ^ 2) :
    |midpointRadius ε η l r - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ M * ε ^ 4 := by
  apply taggedRadius_error hl hr ?_ hq hmesh
  constructor <;> linarith [hq.1, hq.2]

lemma maximumRadius_error {ε η M l r q : ℝ}
    (hl : |l| ≤ 1) (hr : |r| ≤ 1) (hq : q ∈ Icc l r)
    (hmesh : r - l ≤ M * ε ^ 2) :
    |maximumRadius ε η l r - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ M * ε ^ 4 := by
  have hp := max_profile_cell_error hl hr hq
  have hid : maximumRadius ε η l r - (1 / 2 + ε ^ 2 * (profile q + η)) =
      ε ^ 2 * (max (profile l) (profile r) - profile q) := by unfold maximumRadius; ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg ε)]
  calc
    _ ≤ ε ^ 2 * (r - l) := mul_le_mul_of_nonneg_left hp (sq_nonneg ε)
    _ ≤ ε ^ 2 * (M * ε ^ 2) := mul_le_mul_of_nonneg_left hmesh (sq_nonneg ε)
    _ = _ := by ring

lemma radialRadius_error (ε η q : ℝ) :
    radialRadius ε η q - (1 / 2 + ε ^ 2 * (profile q + η)) = 0 := by
  simp [radialRadius, taggedRadius]

lemma taggedRadius_pos {ε η q : ℝ} (hη : 0 ≤ η) : 0 < taggedRadius ε η q := by
  unfold taggedRadius profile
  positivity

lemma midpointRadius_pos {ε η l r : ℝ} (hη : 0 ≤ η) : 0 < midpointRadius ε η l r :=
  taggedRadius_pos hη

lemma maximumRadius_pos {ε η l r : ℝ} (hη : 0 ≤ η) : 0 < maximumRadius ε η l r := by
  have hp : 0 ≤ profile l := by unfold profile; positivity
  have hm : 0 ≤ max (profile l) (profile r) := hp.trans (le_max_left _ _)
  unfold maximumRadius
  positivity

lemma continuous_radialRadius (ε η : ℝ) : Continuous (radialRadius ε η) := by
  unfold radialRadius taggedRadius profile
  fun_prop

theorem ordinary_cell_estimates {ε η M l r q : ℝ}
    (hl : |l| ≤ 1) (hr : |r| ≤ 1) (hq : q ∈ Icc l r)
    (hmesh : r - l ≤ M * ε ^ 2) :
    |secantAlpha l r - (1 + q ^ 2) / 4| ≤ M * ε ^ 2 ∧
    |secantBeta l r - q / 2| ≤ M * ε ^ 2 ∧
    |midpointRadius ε η l r - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ M * ε ^ 4 ∧
    |maximumRadius ε η l r - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ M * ε ^ 4 ∧
    |radialRadius ε η q - (1 / 2 + ε ^ 2 * (profile q + η))| = 0 := by
  refine ⟨?_, ?_, midpointRadius_error hl hr hq hmesh,
    maximumRadius_error hl hr hq hmesh, ?_⟩
  · have h := secantAlpha_error hl hr hq
    linarith only [h, hmesh, hq.1, hq.2]
  · have h := secantBeta_error hq
    linarith only [h, hmesh, hq.1, hq.2]
  · rw [radialRadius_error, abs_zero]

lemma exists_continuous_gluing (N : ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (ha : ∀ j < N, a j ≤ a (j + 1))
    (hf : ∀ j < N, Continuous (f j))
    (hcompat : ∀ j, j + 1 < N → f j (a (j + 1)) = f (j + 1) (a (j + 1))) :
    ∃ L : ℝ → ℝ, Continuous L ∧
      ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)), L q = f j q := by
  classical
  induction N with
  | zero =>
    exact ⟨fun _ => 0, continuous_const, by intro j hj; omega⟩
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨f 0, hf 0 (by omega), ?_⟩
      intro j hj q hq
      have hj0 : j = 0 := by omega
      subst j
      rfl
    · obtain ⟨L, hLcont, hL⟩ := ih (fun j hj => ha j (by omega))
        (fun j hj => hf j (by omega)) (fun j hj => hcompat j (by omega))
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hprev : n - 1 + 1 = n := by omega
      have hjoin : L (a n) = f n (a n) := by
        have h := hL (n - 1) (by omega) (a n) ?_
        · rw [h]
          simpa only [hprev] using hcompat (n - 1) (by omega)
        · rw [hprev]
          exact ⟨by simpa only [hprev] using ha (n - 1) (by omega), le_rfl⟩
      let L' : ℝ → ℝ := fun q => if q ≤ a n then L q else f n q
      have hL' : Continuous L' := by
        apply Continuous.if ?_ hLcont (hf n (by omega))
        intro q hq
        have heq : q = a n := by
          exact Set.mem_singleton_iff.mp (frontier_Iic_subset (a n) hq)
        simpa only [heq] using hjoin
      refine ⟨L', hL', ?_⟩
      intro j hj q hq
      by_cases hjn : j < n
      · have hright : a (j + 1) ≤ a n :=
          GeneralCapArea.partition_monotone (fun k hk => ha k (by omega))
            (by omega) (by omega)
        have hqle : q ≤ a n := hq.2.trans hright
        simpa only [L', ite_eq_left hqle] using hL j hjn q hq
      · have hjn' : j = n := by omega
        subst j
        by_cases hqa : q ≤ a n
        · have heq : q = a n := le_antisymm hqa hq.1
          simpa [L', heq] using hjoin
        · simp only [L', ite_eq_right hqa]

lemma exists_secant_boundary {N : ℕ} {a : ℕ → ℝ}
    (hN : 0 < N) (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j ≤ a (j + 1)) :
    ∃ L : ℝ → ℝ, ContinuousOn L (Icc (-1 : ℝ) 1) ∧ L (-1) = 0 ∧ L 1 = 0 ∧
      ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)),
        secantAlpha (a j) (a (j + 1)) - q * secantBeta (a j) (a (j + 1)) = L q := by
  let f : ℕ → ℝ → ℝ := fun j q =>
    secantAlpha (a j) (a (j + 1)) - q * secantBeta (a j) (a (j + 1))
  have hf : ∀ j < N, Continuous (f j) := by intro j hj; dsimp [f]; fun_prop
  have hcompat : ∀ j, j + 1 < N → f j (a (j + 1)) = f (j + 1) (a (j + 1)) := by
    intro j hj
    dsimp [f]
    rw [shared_right, shared_left]
  obtain ⟨L, hLc, hL⟩ := exists_continuous_gluing N a f ha hf hcompat
  refine ⟨L, hLc.continuousOn, ?_, ?_, ?_⟩
  · have h := hL 0 hN (a 0) ⟨le_rfl, ha 0 hN⟩
    rw [← ha0, h]
    dsimp [f]
    rw [shared_left, ha0]
    norm_num
  · have hlast : N - 1 + 1 = N := by omega
    have h := hL (N - 1) (by omega) (a N) ?_
    · rw [← haN, h]
      dsimp [f]
      rw [hlast, shared_right, haN]
      norm_num
    · rw [hlast]
      exact ⟨by simpa only [hlast] using ha (N - 1) (by omega), le_rfl⟩
  · intro j hj q hq
    exact (hL j hj q hq).symm

theorem ordinaryData_admissible (choice : CapChoice) {N : ℕ} {a : ℕ → ℝ}
    {ε η M : ℝ} (hN : 0 < N) (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j < a (j + 1)) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hmesh : ∀ j < N, a (j + 1) - a j ≤ M * ε ^ 2) :
    AngularGeneral.Admissible ε η M (ordinaryData choice N a ε η) := by
  have hmono : ∀ j < N, a j ≤ a (j + 1) := fun j hj => (ha j hj).le
  have hbound : ∀ j ≤ N, |a j| ≤ 1 := by
    intro j hj
    have hl : a 0 ≤ a j := GeneralCapArea.partition_monotone hmono (Nat.zero_le j) hj
    have hr : a j ≤ a N := GeneralCapArea.partition_monotone hmono hj le_rfl
    rw [ha0] at hl
    rw [haN] at hr
    exact abs_le.mpr ⟨hl, hr⟩
  obtain ⟨L, hLc, hL0, hL1, hL⟩ := exists_secant_boundary hN ha0 haN hmono
  refine ⟨hN, ha0, haN, ha, hbound, ⟨L, hLc, hL0, hL1, hL⟩, ?_, ?_, ?_⟩
  · intro j hj
    cases choice with
    | midpoint => exact continuous_const.continuousOn
    | maximum => exact continuous_const.continuousOn
    | radial => exact (continuous_radialRadius ε η).continuousOn
  · intro j hj q hq
    cases choice with
    | midpoint => exact midpointRadius_pos hη
    | maximum => exact maximumRadius_pos hη
    | radial => exact taggedRadius_pos hη
  · intro j hj q hq
    change j < N at hj
    have h := ordinary_cell_estimates (η := η) (hbound j (by omega)) (hbound (j + 1) (by omega))
      hq (hmesh j hj)
    refine ⟨h.1, h.2.1, ?_⟩
    cases choice with
    | midpoint => exact h.2.2.1
    | maximum => exact h.2.2.2.1
    | radial =>
      change |radialRadius ε η q - (1 / 2 + ε ^ 2 * (GeneralCapArea.profile q + η))| ≤ M * ε ^ 4
      rw [h.2.2.2.2]
      positivity

end CylinderCovering.AngularOrdinaryCaps

end OAI
