import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryRangeScales

namespace OAI

/-! # Floor lengths for cofactors in the small power auxiliary band -/
namespace JointDickman
open Filter
open scoped Topology

theorem auxiliary_cofactor_floor_scales :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → a ≤ (N:ℝ)^(1/4:ℝ) →
      (N:ℝ)^(1/2:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ) ∧
      (N:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 ∧
      (⌊(2*N:ℝ)/a⌋₊:ℝ) ≤ 2*(N:ℝ) := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with N hquarter hN a ha haN
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have ha0 : 0<a := by linarith
  have hs : 1 ≤ (N:ℝ)^(1/2:ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hidentity : (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ)*(N:ℝ)^(1/4:ℝ)=N := by
    rw [← Real.rpow_add hn,← Real.rpow_add hn]
    norm_num
  have hx : 2*(N:ℝ)^(1/2:ℝ) ≤ (N:ℝ)/a := by
    apply (le_div_iff₀ ha0).mpr
    calc
      _ ≤ 2*(N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ) := by gcongr
      _ ≤ (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ)*(N:ℝ)^(1/4:ℝ) := by
        change 2 ≤ (N:ℝ)^(1/4:ℝ) at hquarter
        nlinarith only [hquarter,show 0 ≤ (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/4:ℝ) by positivity]
      _ = _ := hidentity
  have hfloor := Nat.lt_floor_add_one ((N:ℝ)/a)
  have hm : (N:ℝ)^(1/2:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ) := by nlinarith
  have hmn : ⌊(N:ℝ)/a⌋₊ ≤ ⌊(2*N:ℝ)/a⌋₊ := by
    apply Nat.floor_mono
    gcongr
    linarith
  have hns : (N:ℝ)^(1/2:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ) :=
    hm.trans (by exact_mod_cast hmn)
  refine ⟨hm,?_,?_⟩
  · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (N:ℝ)^(1/2:ℝ)) hns 2
    have he : ((N:ℝ)^(1/2:ℝ))^2=N := by rw [← Real.rpow_mul_natCast hn.le]; norm_num
    rwa [he] at hh
  · have hf := Nat.floor_le (by positivity : 0 ≤ (2*N:ℝ)/a)
    apply hf.trans
    apply (div_le_iff₀ ha0).mpr
    nlinarith

end JointDickman

end OAI
