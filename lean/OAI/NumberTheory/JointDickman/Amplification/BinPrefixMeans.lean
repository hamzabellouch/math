import OAI.NumberTheory.JointDickman.Analysis.BinCharacters

namespace OAI

/-! # Ordinary prefix means of the finite bin labels -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem sum_Ioc_zero_eq_range_add {R : Type*} [AddCommGroup R] (f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = (∑ n ∈ range N, f n)+f N-f 0 := by
  have hs : insert 0 (Ioc 0 N) = range (N+1) := by
    ext n
    simp only [mem_insert,mem_Ioc,mem_range]
    omega
  have hh := congrArg (fun S : Finset ℕ => ∑ n ∈ S, f n) hs
  rw [sum_insert (by simp),sum_range_succ] at hh
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using hh

theorem binLabel_endpoint_div_tendsto_zero {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) :
    Tendsto (fun N : ℕ => binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) ζ N/(N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun N : ℕ => 1/(N : ℝ))
  · intro N
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_binLabel_le_one _ ζ hζ N) (Nat.cast_nonneg N)
  · exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1

theorem binLabel_prefix_mean
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) ζ n)/(N : ℂ)) atTop
      (𝓝 (binDistributionMean ν ζ)) := by
  have hi := (canonical_binLabel_mean hJ ν hν ζ (by norm_num : (0 : ℝ) < 1)).comp tendsto_natCast_atTop_atTop
  have he := binLabel_endpoint_div_tendsto_zero ζ hζ
  have hres := hi.sub he
  convert hres using 1
  · funext N
    simp only [Function.comp_apply,one_mul,Nat.floor_natCast,Complex.ofReal_natCast,Complex.ofReal_one,
      sum_Ioc_zero_eq_range_add,binLabel_apply_zero,sub_zero,add_div]
    ring
  · simp only [sub_zero,binDistributionMean]

end JointDickman

end OAI
