import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

namespace UniformKServer.OfflineDynamic
variable {n k : ℕ} [NeZero k]

def minimum (c : Fin k → ℚ) : ℚ :=
  (Finset.univ.image c).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def optRat (d : RationalMetric n) : Configuration n k → List (Fin n) → ℚ
  | _, [] => 0
  | s, r::w => minimum (fun j => d.distance (s j) r + optRat d (serve s r j) w)

theorem minimum_le (c : Fin k → ℚ) (j : Fin k) : minimum c ≤ c j := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem minimum_attained (c : Fin k → ℚ) : ∃ j, minimum c = c j := by
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image c)
    (Finset.image_nonempty.mpr Finset.univ_nonempty))
  exact ⟨j, he.symm⟩

theorem optRat_attained (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    ∃ h : History n k, h.map Prod.fst = w ∧ costAlong d s h = (optRat d s w : ℝ) := by
  induction w generalizing s with
  | nil => exact ⟨[], rfl, by simp [costAlong,optRat]⟩
  | cons r w ih =>
    obtain ⟨j,hj⟩ := minimum_attained (fun j => d.distance (s j) r + optRat d (serve s r j) w)
    obtain ⟨h,hh,hcost⟩ := ih (serve s r j)
    refine ⟨(r,j)::h, by simp only [List.map_cons,hh], ?_⟩
    simp only [optRat, hj, costAlong, Rat.cast_add, hcost]

theorem optRat_lower (d : RationalMetric n) (s : Configuration n k) (h : History n k) :
    (optRat d s (h.map Prod.fst) : ℝ) ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => simp [optRat,costAlong]
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    have hj := minimum_le (fun j => d.distance (s j) r + optRat d (serve s r j) (h.map Prod.fst)) j
    have hj' : (minimum (fun j => d.distance (s j) r + optRat d (serve s r j) (h.map Prod.fst)) : ℝ) ≤
      (d.distance (s j) r : ℝ)+(optRat d (serve s r j) (h.map Prod.fst) : ℝ) := by exact_mod_cast hj
    exact hj'.trans (add_le_add (le_refl _) (ih (serve s r j)))

theorem offline_eq_optRat (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    offlineCost d s w = (optRat d s w : ℝ) := by
  obtain ⟨h,hh,hcost⟩ := optRat_attained d s w
  apply le_antisymm
  · apply csInf_le
    · refine ⟨(optRat d s w : ℝ), ?_⟩
      rintro c ⟨g,hg,rfl⟩
      rw [← hg]
      exact optRat_lower d s g
    · exact ⟨h,hh,hcost.symm⟩
  · apply le_csInf
    · exact ⟨costAlong d s h, h, hh, rfl⟩
    · rintro c ⟨g,hg,rfl⟩
      rw [← hg]
      exact optRat_lower d s g

end UniformKServer.OfflineDynamic

/-!
Exact rational minimization used by uniform-computation Section 02,
Proposition `prop:finite-table`, paragraph "Exact rational attainment".
An affine row is constrained to be ≤ 0. The last coordinate is the
nonnegative objective a; all other coordinates are eliminated in order.
The algorithm is executable rational arithmetic; no real optimization oracle.
-/

end OAI
