import Mathlib

namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

def clusterScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

theorem clusterScale_pos (j : ℕ) : 0 < clusterScale j := by
  unfold clusterScale
  positivity

theorem clusterScale_add (j n : ℕ) :
    clusterScale (j + n) = clusterScale j * (1 / 2 : ℝ) ^ n := by
  unfold clusterScale
  rw [show j + n + 1 = (j + 1) + n by omega, pow_add]

theorem clusterScale_antitone : Antitone clusterScale := by
  intro i j hij
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.add_le_add_right hij 1)
  exact h

theorem clusterScale_half {i j : ℕ} (hij : i < j) :
    clusterScale j ≤ clusterScale i / 2 := by
  calc
    clusterScale j ≤ clusterScale (i + 1) := clusterScale_antitone (by omega)
    _ = clusterScale i / 2 := by rw [clusterScale_add]; norm_num; ring

theorem clusterScale_tendsto : Tendsto clusterScale atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact h.comp (tendsto_add_atTop_nat 1)

                                            
theorem cluster_norm_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {v z : B} (hv : ‖v‖ = 1) {j : ℕ}
    (hz : dist z (clusterScale j • v) ≤ clusterScale j / 100) :
    ‖z‖ ≤ (101 / 100 : ℝ) * clusterScale j := by
  have hcent : dist (clusterScale j • v) 0 = clusterScale j := by
    simp [dist_zero_right, norm_smul, hv, Real.norm_eq_abs, abs_of_pos (clusterScale_pos j)]
  have ht := dist_triangle z (clusterScale j • v) 0
  rw [dist_zero_right, hcent] at ht
  linarith

                                                                               
theorem cluster_separation {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {v p q : B} (hv : ‖v‖ = 1) {i j : ℕ} (hij : i < j)
    (hp : dist p (clusterScale i • v) ≤ clusterScale i / 100)
    (hq : dist q (clusterScale j • v) ≤ clusterScale j / 100) :
    (97 / 200 : ℝ) * clusterScale i ≤ dist p q := by
  have ha := clusterScale_half hij
  have hi := clusterScale_pos i
  have hj := clusterScale_pos j
  have hcent : dist (clusterScale i • v) (clusterScale j • v) =
      clusterScale i - clusterScale j := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have ht := dist_triangle4 (clusterScale i • v) p q (clusterScale j • v)
  rw [hcent, dist_comm (clusterScale i • v) p] at ht
  linarith

                                                                           
                                                                             
theorem five_scales {r : ℝ} (hr : 0 < r) (s : Finset ℕ)
    (hlo : ∀ j ∈ s, r / 4 < clusterScale j)
    (hhi : ∀ j ∈ s, clusterScale j ≤ (400 / 97 : ℝ) * r) : s.card ≤ 5 := by
  classical
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    have hi : i ∈ s := s.min'_mem hs
    have hsub : s ⊆ Finset.Icc i (i + 4) := by
      intro j hj
      have hij : i ≤ j := s.min'_le j hj
      have hji : j ≤ i + 4 := by
        by_contra! hj'
        have hd : clusterScale j ≤ clusterScale i / 32 := by
          calc
            clusterScale j ≤ clusterScale (i + 5) := clusterScale_antitone (by omega)
            _ = clusterScale i / 32 := by rw [clusterScale_add]; norm_num; ring
        have h1 := hlo j hj
        have h2 := hhi i hi
        linarith
      exact Finset.mem_Icc.mpr ⟨hij, hji⟩
    calc
      s.card ≤ (Finset.Icc i (i + 4)).card := Finset.card_le_card hsub
      _ = 5 := by simp; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end CompactBanach
end

end OAI
