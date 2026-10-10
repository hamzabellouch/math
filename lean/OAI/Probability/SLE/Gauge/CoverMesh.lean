import Mathlib

namespace OAI

/-!
The deterministic common mesh in the dense-cover construction. At each
stage there are only finitely many positive test cutoffs. The mesh satisfies
every cutoff and decreases by at least a factor of two at each stage.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.CoverMesh

def cutoff (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact (insert 1 ((I n).image (ε n))).min' (by simp)

lemma cutoff_pos (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i ∈ I n → 0 < ε n i) (n : ℕ) : 0 < cutoff I ε n := by
  classical
  unfold cutoff
  have hmem := Finset.min'_mem (insert 1 ((I n).image (ε n))) (by simp)
  rcases Finset.mem_insert.mp hmem with h | h
  · simpa only [h] using (show (0 : ℝ) < 1 by norm_num)
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact he ▸ hε n i hi

lemma cutoff_le_one (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) :
    cutoff I ε n ≤ 1 := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

lemma cutoff_le_test (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (n i : ℕ) (hi : i ∈ I n) : cutoff I ε n ≤ ε n i := by
  classical
  exact Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

def mesh (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) : ℕ → ℝ
  | 0 => cutoff I ε 0
  | n + 1 => min (mesh I ε n / 2) (cutoff I ε (n + 1))

lemma mesh_pos (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i ∈ I n → 0 < ε n i) (n : ℕ) : 0 < mesh I ε n := by
  induction n with
  | zero => exact cutoff_pos I ε hε 0
  | succ n ih =>
      exact lt_min (div_pos ih (by norm_num)) (cutoff_pos I ε hε (n + 1))

lemma mesh_half (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) :
    mesh I ε (n + 1) ≤ mesh I ε n / 2 := min_le_left _ _

lemma mesh_le_cutoff (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) :
    mesh I ε n ≤ cutoff I ε n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

lemma mesh_le_test (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (n i : ℕ) (hi : i ∈ I n) : mesh I ε n ≤ ε n i :=
  (mesh_le_cutoff I ε n).trans (cutoff_le_test I ε n i hi)

lemma mesh_le_half_pow (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) :
    mesh I ε n ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simpa only [mesh, pow_zero] using cutoff_le_one I ε 0
  | succ n ih =>
      calc
        mesh I ε (n + 1) ≤ mesh I ε n / 2 := mesh_half I ε n
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

lemma mesh_le_dyadic (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ) (n : ℕ) :
    mesh I ε n ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
  convert mesh_le_half_pow I ε n using 1
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [one_div, inv_pow]

lemma mesh_tendsto_zero (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i ∈ I n → 0 < ε n i) :
    Tendsto (mesh I ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => (mesh_pos I ε hε n).le) (mesh_le_half_pow I ε)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- One positive deterministic mesh works for every finite test window,
including empty windows, and tends to zero with geometric decay. -/
theorem exists_common_mesh (I : ℕ → Finset ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i ∈ I n → 0 < ε n i) :
    ∃ v : ℕ → ℝ, (∀ n, 0 < v n) ∧
      (∀ n, v n ≤ (2 : ℝ) ^ (-(n : ℝ))) ∧
      (∀ n, v (n + 1) ≤ v n / 2) ∧
      (∀ n i, i ∈ I n → v n ≤ ε n i) ∧ Tendsto v atTop (𝓝 0) :=
  ⟨mesh I ε, mesh_pos I ε hε, mesh_le_dyadic I ε, mesh_half I ε,
    mesh_le_test I ε, mesh_tendsto_zero I ε hε⟩

end SLEExactGauge.CoverMesh

end

end OAI
