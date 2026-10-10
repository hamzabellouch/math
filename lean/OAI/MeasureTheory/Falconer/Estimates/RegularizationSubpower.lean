import OAI.MeasureTheory.Falconer.Estimates.ClassPruning
import OAI.MeasureTheory.Falconer.Estimates.RegularizationScales
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

namespace PlanarFalconer
open Filter
open scoped Topology ENNReal

theorem regularization_fixed_count_bound (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N (N/H))).card ≤
      (4*N+1)^(2*H+1) := by
  have hc := regularization_label_count Q μ N (N/H)
  have hs := (division_blocks_control hH hN).2
  calc
    _ ≤ (2*N+1)^(N/(N/H)+1)*(4*N+1) := hc
    _ ≤ (4*N+1)^(2*H)*(4*N+1) := by
      apply Nat.mul_le_mul_right
      exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hs)
    _ = _ := (pow_succ _ _).symm

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((4*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((5:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (5:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (5:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : (4*(N:ℝ)+1)^k ≤ (5:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

theorem regularization_class_count_subpower (H : ℕ) (hH : 0 < H)
    {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane),
      (((regularizationLeaves Q μ N).image (regularizationLabel Q μ N (N/H))).card:ℝ) ≤
        ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_polynomial_subpower (2*H+1) he
  refine ⟨max H N₁,?_⟩
  intro N hN Q μ
  have hh := regularization_fixed_count_bound Q μ hH ((le_max_left H N₁).trans hN)
  have hhR : (((regularizationLeaves Q μ N).image (regularizationLabel Q μ N (N/H))).card:ℝ) ≤
      (4*(N:ℝ)+1)^(2*H+1) := by exact_mod_cast hh
  exact hhR.trans (hN₁ N ((le_max_right H N₁).trans hN))

theorem thin_leaf_loss_identity (N : ℕ) :
    (4:ENNReal)^N*((2:ENNReal)^(4*N))⁻¹ = ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  have htwo : (2:ENNReal) ≠ 0 := by norm_num
  have htwofin : (2:ENNReal) ≠ ⊤ := by norm_num
  have hleft : (4:ENNReal)^N*((2:ENNReal)^(4*N))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.inv_ne_top.mpr (pow_ne_zero _ htwo))
  rw [← ENNReal.ofReal_toReal hleft]
  apply congrArg ENNReal.ofReal
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  rw [Real.rpow_neg (by positivity),Real.rpow_two]
  have h4 : (4:ℝ)^N = ((2:ℝ)^N)^2 := by rw [← pow_mul, Nat.mul_comm N 2, pow_mul]; norm_num
  have hpow : (2:ℝ)^(4*N) = ((2:ℝ)^N)^4 := by rw [Nat.mul_comm 4 N,pow_mul]
  rw [h4,hpow]
  field_simp

end PlanarFalconer

end OAI
