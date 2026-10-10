import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.RegularLatticeScales

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem exists_annular_lattice_depth (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ t : ℕ, latticeRadius R (k + t) ≤ r / 8 := by
  obtain ⟨t, ht⟩ := ((latticeRadius_tendsto_zero (latticeRadius R k)).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < r / 8))).exists
  refine ⟨t, ?_⟩
  rw [latticeRadius_add]
  exact ht.le

def annularLatticeDepth (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) : ℕ := by
  classical
  exact Nat.find (exists_annular_lattice_depth R k r hr)

theorem annularLatticeDepth_radius_upper (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) :
    latticeRadius R (k + annularLatticeDepth R k r hr) ≤ r / 8 := by
  classical
  exact Nat.find_spec (exists_annular_lattice_depth R k r hr)

theorem annularLatticeDepth_minimal (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℕ) (ht : latticeRadius R (k + t) ≤ r / 8) :
    annularLatticeDepth R k r hr ≤ t := by
  classical
  exact Nat.find_min' (exists_annular_lattice_depth R k r hr) ht

theorem annularLatticeDepth_antitone (R : ℝ) (k : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    annularLatticeDepth R k s hs ≤ annularLatticeDepth R k r hr :=
  annularLatticeDepth_minimal R k s hs _
    ((annularLatticeDepth_radius_upper R k r hr).trans (by linarith))

theorem annularLatticeDepth_radius_lower (R : ℝ) (hR : 0 < R) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ 8 * latticeRadius R k) :
    r ≤ 512 * latticeRadius R (k + annularLatticeDepth R k r hr) := by
  generalize hd : annularLatticeDepth R k r hr = t
  cases t with
  | zero =>
    simp only [Nat.add_zero]
    have hp := latticeRadius_pos R hR k
    linarith
  | succ t =>
    have hp : r / 8 < latticeRadius R (k + t) := by
      by_contra hbad
      have hm := annularLatticeDepth_minimal R k r hr t (le_of_not_gt hbad)
      rw [hd] at hm
      omega
    rw [← Nat.add_assoc, latticeRadius_succ]
    linarith

theorem annularLatticeDepth_pos (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrtop : r < 8 * latticeRadius R k) : 0 < annularLatticeDepth R k r hr := by
  have hu := annularLatticeDepth_radius_upper R k r hr
  by_contra ht
  have hz : annularLatticeDepth R k r hr = 0 := by omega
  rw [hz, Nat.add_zero] at hu
  linarith

theorem exists_uniform_annular_lattice_depth (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ I : ℕ, 0 < I ∧ ∀ (R : ℝ), 0 < R → ∀ (k : ℕ) (r : ℝ) (hr : 0 < r),
      ρ * latticeRadius R k ≤ r → annularLatticeDepth R k r hr ≤ I := by
  obtain ⟨j, hj⟩ := exists_annular_lattice_depth 1 0 ρ hρ
  refine ⟨j + 1, by omega, ?_⟩
  intro R hR k r hr hmin
  apply annularLatticeDepth_minimal R k r hr (j + 1)
  have hi : latticeRadius 1 (j + 1) ≤ ρ / 8 :=
    (latticeRadius_antitone 1 (by norm_num) (Nat.le_succ j)).trans (by simpa using! hj)
  have hp := latticeRadius_pos R hR k
  calc
    _ = latticeRadius R k * latticeRadius 1 (j + 1) := by rw [latticeRadius_add]; simp [latticeRadius]
    _ ≤ latticeRadius R k * (ρ / 8) := mul_le_mul_of_nonneg_left hi hp.le
    _ ≤ r / 8 := by linarith

end

end RieszRectifiability

end OAI
