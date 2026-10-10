import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileChain
import OAI.Probability.SKBarriers.Parisi.CDFQuantileInverse

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem fin_sum_below {r n : ℕ} (hr : r ≤ n) (a : ℝ) :
    (∑ j : Fin n, if j.val < r then a else 0)=(r:ℝ)*a := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < r then a else 0) n,← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j < r)=Finset.range r := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem quantileCDF_uniformCDFQuantiles_error (k : ℕ) (α : StieltjesFunction ℝ)
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |quantileCDF k (uniformCDFQuantiles k α) x-α x| ≤ ((k+1:ℕ):ℝ)⁻¹ := by
  have hN : (0:ℝ)<(k+1:ℕ) := by positivity
  have ht (j : Fin (k+1)) : ((j.val:ℝ)+1)/((k+1:ℕ):ℝ) ≤ 1 := by
    apply (div_le_one hN).mpr
    exact_mod_cast j.isLt
  let a : ℝ := ((k+1:ℕ):ℝ)*α x
  have ha : 0 ≤ a := mul_nonneg hN.le (hα x).1
  have hfloor : ⌊a⌋₊ ≤ k+1 := by
    have H := (Nat.floor_le ha).trans (mul_le_of_le_one_right hN.le (hα x).2)
    exact_mod_cast H
  have he (j : Fin (k+1)) : uniformCDFQuantiles k α j ≤ x ↔ j.val < ⌊a⌋₊ := by
    rw [uniformCDFQuantiles,supportedCDFQuantile_le_iff α hα1 (ht j) hx,div_le_iff₀ hN]
    constructor
    · intro h
      have H : (j.val+1:ℕ) ≤ ⌊a⌋₊ := Nat.le_floor (by dsimp [a]; push_cast at h ⊢; nlinarith)
      omega
    · intro h
      have H : (j.val:ℝ)+1 ≤ (⌊a⌋₊:ℝ) := by exact_mod_cast h
      have H' := H.trans (Nat.floor_le ha)
      dsimp [a] at H'
      nlinarith
  rw [quantileCDF_formula]
  simp_rw [he]
  rw [fin_sum_below hfloor]
  change |(⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ)-α x| ≤ ((k+1:ℕ):ℝ)⁻¹
  have H : (⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ) ≤ α x := by
    apply (div_le_iff₀ hN).mpr
    simpa only [a,mul_comm] using Nat.floor_le ha
  rw [abs_of_nonpos (sub_nonpos.mpr H),neg_sub]
  have ee : α x-(⌊a⌋₊:ℝ)/((k+1:ℕ):ℝ)=(a-(⌊a⌋₊:ℝ))/((k+1:ℕ):ℝ) := by
    dsimp [a]
    field_simp
  rw [ee,inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ hN.le
  linarith [Nat.lt_floor_add_one a]

theorem uniformCDFQuantiles_L1_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) :
    Tendsto (fun k => ∫ x in Icc (0:ℝ) 1,
      |quantileCDF k (uniformCDFQuantiles k α) x-α x|) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun k : ℕ => ((k+1:ℕ):ℝ)⁻¹)
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) (fun k => ?_) ?_
  · have hi : IntegrableOn (fun x => |quantileCDF k (uniformCDFQuantiles k α) x-α x|) (Icc (0:ℝ) 1) :=
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc ((quantileCDF_monotone k (uniformCDFQuantiles k α)).monotoneOn _)).sub
        (MonotoneOn.integrableOn_isCompact isCompact_Icc (α.mono.monotoneOn _))).abs
    have H := setIntegral_mono_on hi
      (integrableOn_const (s := Icc (0:ℝ) 1) (μ := volume) (C := ((k+1:ℕ):ℝ)⁻¹) (by simp)) measurableSet_Icc
      (fun x hx => quantileCDF_uniformCDFQuantiles_error k α hα hα1 hx)
    simpa using H
  · simpa only [Nat.cast_add,Nat.cast_one,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end SK.Analytic

end
end

end OAI
