import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Trees.CompletionGeometry

namespace OAI

namespace BinPackingGap.Geometry

variable {m R : ℕ}

def posLT (r s : Position m R) : Prop :=
  r.1.val < s.1.val ∨ r.1 = s.1 ∧ r.2.val < s.2.val

def posLE (r s : Position m R) : Prop := r = s ∨ posLT r s

theorem posLT_irrefl (r : Position m R) : ¬ posLT r r := by
  simp [posLT]

theorem posLT_trans {r s t : Position m R}
    (hrs : posLT r s) (hst : posLT s t) : posLT r t := by
  simp only [posLT, Fin.ext_iff] at *
  omega

theorem posLT_asymm {r s : Position m R} (h : posLT r s) : ¬ posLT s r :=
  fun h' => posLT_irrefl r (posLT_trans h h')

theorem posLT_trichotomy (r s : Position m R) :
    posLT r s ∨ r = s ∨ posLT s r := by
  simp only [posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem posLT_or_posLT_of_ne {r s : Position m R} (hne : r ≠ s) :
    posLT r s ∨ posLT s r := by
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · exact Or.inl hrs
  · exact (hne hrs).elim
  · exact Or.inr hsr

theorem posLE_iff_not_posLT {r s : Position m R} : posLE r s ↔ ¬ posLT s r := by
  simp only [posLE, posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem posLE_refl (r : Position m R) : posLE r r := Or.inl rfl

theorem posLE_trans {r s t : Position m R}
    (hrs : posLE r s) (hst : posLE s t) : posLE r t := by
  rcases hrs with rfl | hrs
  · exact hst
  rcases hst with rfl | hst
  · exact Or.inr hrs
  exact Or.inr (posLT_trans hrs hst)

theorem heightCode_ge_theta (R : ℕ) (r : Position m R) :
    theta R r.1 ≤ heightCode R r := by
  have hj : (0 : ℚ) ≤ r.2.val := Nat.cast_nonneg _
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  unfold theta heightCode
  nlinarith

theorem heightCode_le_edgeMax (R : ℕ) (r : Position m R) :
    heightCode R r ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val - 1 := by
  have hj : (r.2.val : ℚ) + 1 ≤ R := by
    exact_mod_cast Nat.succ_le_of_lt r.2.isLt
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_right hj hp
  unfold heightCode
  linarith

theorem heightCode_same_edge_sub (R : ℕ) (e : Fin m) (j k : Fin R) :
    heightCode R (e, k) - heightCode R (e, j) =
      ((k.val : ℚ) - j.val) * ((R : ℚ) + 1) ^ e.val := by
  unfold heightCode
  ring

theorem heightCode_next_rep_sub (R : ℕ) (e : Fin m) (j k : Fin R)
    (hnext : k.val = j.val + 1) :
    heightCode R (e, k) - heightCode R (e, j) = ((R : ℚ) + 1) ^ e.val := by
  rw [heightCode_same_edge_sub]
  have hk : (k.val : ℚ) = (j.val : ℚ) + 1 := by exact_mod_cast hnext
  rw [hk]
  ring

theorem heightCode_next_edge_sub (R : ℕ) (e f : Fin m) (j k : Fin R)
    (hnext : f.val = e.val + 1) (hlast : j.val + 1 = R) (hfirst : k.val = 0) :
    heightCode R (f, k) - heightCode R (e, j) = ((R : ℚ) + 1) ^ e.val := by
  have hj : (j.val : ℚ) + 1 = R := by exact_mod_cast hlast
  change ((k.val : ℚ) + 1) * ((R : ℚ) + 1) ^ f.val - 1 -
    (((j.val : ℚ) + 1) * ((R : ℚ) + 1) ^ e.val - 1) = _
  rw [hnext, hfirst, hj, pow_succ]
  ring

theorem theta_next_sub (R : ℕ) (e f : Fin m) (hnext : f.val = e.val + 1) :
    theta R f - theta R e = (R : ℚ) * ((R : ℚ) + 1) ^ e.val := by
  unfold theta
  rw [hnext, pow_succ]
  ring

theorem heightCode_jump {r s : Position m R} (h : posLT r s) :
    theta R r.1 + 1 ≤ heightCode R s - heightCode R r := by
  rcases h with he | ⟨he, hj⟩
  · have hp : ((R : ℚ) + 1) ^ (r.1.val + 1) ≤
        ((R : ℚ) + 1) ^ s.1.val :=
      pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt he)
    rw [pow_succ] at hp
    have hlo := heightCode_ge_theta R s
    have hhi := heightCode_le_edgeMax R r
    unfold theta at hlo ⊢
    nlinarith
  · have hj' : (r.2.val : ℚ) + 1 ≤ s.2.val := by
      exact_mod_cast Nat.succ_le_of_lt hj
    have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
    have hmul := mul_le_mul_of_nonneg_right hj' hp
    simp only [heightCode, theta, ← he]
    nlinarith

theorem theta_jump {e f : Fin m} (hef : e < f) :
    (R : ℚ) * ((R : ℚ) + 1) ^ e.val ≤ theta R f - theta R e := by
  have hp : ((R : ℚ) + 1) ^ (e.val + 1) ≤ ((R : ℚ) + 1) ^ f.val :=
    pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt hef)
  rw [pow_succ] at hp
  unfold theta
  nlinarith

theorem theta_jump_ge_heightCode {r : Position m R} {f : Fin m} (hef : r.1 < f) :
    heightCode R r + 1 ≤ theta R f - theta R r.1 :=
  (by linarith [heightCode_le_edgeMax R r] :
    heightCode R r + 1 ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val).trans (theta_jump hef)

theorem heightCode_strictMono {r s : Position m R} (h : posLT r s) :
    heightCode R r < heightCode R s := by
  have hjump := heightCode_jump h
  have hn := theta_nonneg R r.1
  linarith

theorem heightCode_lt_iff {r s : Position m R} :
    heightCode R r < heightCode R s ↔ posLT r s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact hrs
    · subst s
      exact (lt_irrefl _ h).elim
    · exact (not_lt_of_ge (heightCode_strictMono hsr).le h).elim
  · exact heightCode_strictMono

theorem baseline_gap_of_posLT {r s : Position m R} (h : posLT r s) :
    gap m R ≤ baseline m R s - baseline m R r := by
  have hjump := heightCode_jump h
  have ht := theta_nonneg R r.1
  have hheight : (1 : ℚ) ≤ heightCode R s - heightCode R r := by linarith
  have hmul := mul_le_mul_of_nonneg_left hheight (gap_pos m R).le
  unfold baseline
  nlinarith

theorem gap_le_abs_baseline_sub {r s : Position m R} (hne : r ≠ s) :
    gap m R ≤ |baseline m R s - baseline m R r| := by
  rcases posLT_or_posLT_of_ne hne with hrs | hsr
  · exact (baseline_gap_of_posLT hrs).trans (le_abs_self _)
  · rw [abs_sub_comm]
    exact (baseline_gap_of_posLT hsr).trans (le_abs_self _)

theorem baseline_lt_iff {r s : Position m R} :
    baseline m R r < baseline m R s ↔ posLT r s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact hrs
    · subst s
      exact (lt_irrefl _ h).elim
    · have hg := baseline_gap_of_posLT hsr
      have hp := gap_pos m R
      linarith
  · intro h
    have hg := baseline_gap_of_posLT h
    have hp := gap_pos m R
    linarith

theorem baseline_le_iff {r s : Position m R} :
    baseline m R r ≤ baseline m R s ↔ posLE r s := by
  rw [posLE_iff_not_posLT, ← baseline_lt_iff]
  constructor
  · intro hle hlt
    linarith
  · intro h
    by_contra h'
    apply h
    linarith

theorem baseline_eq_iff {r s : Position m R} :
    baseline m R r = baseline m R s ↔ r = s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact (ne_of_lt (baseline_lt_iff.mpr hrs) h).elim
    · exact hrs
    · exact (ne_of_lt (baseline_lt_iff.mpr hsr) h.symm).elim
  · rintro rfl
    rfl

theorem baseline_le_jobInterior_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - Δ / 2 ↔ posLT s r := by
  constructor
  · intro hs
    apply baseline_lt_iff.mp
    linarith
  · intro hsr
    have hgap := baseline_gap_of_posLT hsr
    linarith

theorem jobInterior_lt_baseline_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    baseline m R r - Δ / 2 < baseline m R s ↔ posLE r s := by
  rw [posLE_iff_not_posLT, ← baseline_le_jobInterior_iff hΔ hΔg]
  exact lt_iff_not_ge

theorem jobInterior_mem_current {Δ : ℚ} (hΔ : 0 < Δ) (r : Position m R) :
    baseline m R r - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R r := by
  constructor <;> linarith

theorem jobInterior_mem_job_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    (baseline m R s - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R s) ↔ s = r := by
  constructor
  · rintro ⟨hleft, hright⟩
    rcases posLT_trichotomy s r with hsr | hsr | hrs
    · have hp := (baseline_le_jobInterior_iff hΔ hΔg).mpr hsr
      linarith
    · exact hsr
    · have hgap := baseline_gap_of_posLT hrs
      linarith
  · intro hsr
    subst s
    exact jobInterior_mem_current hΔ r

theorem baseline_le_actualJobInterior_iff (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - delta m R D L / 2 ↔ posLT s r :=
  baseline_le_jobInterior_iff (delta_pos m R D L) (delta_lt_gap m R D L)

theorem actualJobInterior_mem_job_iff (D L : ℕ) {r s : Position m R} :
    (baseline m R s - delta m R D L ≤ baseline m R r - delta m R D L / 2 ∧
      baseline m R r - delta m R D L / 2 < baseline m R s) ↔ s = r :=
  jobInterior_mem_job_iff (delta_pos m R D L) (delta_lt_gap m R D L)

end BinPackingGap.Geometry

end OAI
