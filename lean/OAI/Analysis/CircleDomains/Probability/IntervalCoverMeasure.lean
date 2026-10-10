import OAI.Analysis.CircleDomains.Rigidity.TraceLineTails

namespace OAI

/-! The quantitative measure step in the slice estimate. Connected fiber
coverage pays through domain images, null common traces and disk intervals. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem interval_length_le_image_and_tolls {ι : Type*} [Countable ι]
    {a b : ℝ} {E N : Set ℝ} {I : ι → Set ℝ} (hN : volume N = 0)
    (hcover : uIcc a b ⊆ E ∪ N ∪ ⋃ j, I j) :
    ENNReal.ofReal |b-a| ≤ volume E + ∑' j, volume (I j) := by
  calc
    _ = volume (uIcc a b) := by
      rw [← Icc_min_max,Real.volume_Icc,max_sub_min_eq_abs,abs_sub_comm]
    _ ≤ volume (E ∪ N ∪ ⋃ j, I j) := measure_mono hcover
    _ ≤ volume (E ∪ N) + volume (⋃ j, I j) := measure_union_le _ _
    _ ≤ (volume E + volume N) + ∑' j, volume (I j) :=
      add_le_add (measure_union_le _ _) (measure_iUnion_le _)
    _ = _ := by rw [hN,add_zero]

 theorem interval_length_le_integral_and_tolls {ι : Type*} [Countable ι]
    {a b C : ℝ} {s : ι → ℝ} {E N : Set ℝ} {I : ι → Set ℝ}
    (hC : 0 ≤ C) (hs : ∀ j, 0 ≤ s j) (hsum : Summable s)
    (hN : volume N = 0) (hE : volume E ≤ ENNReal.ofReal C)
    (hI : ∀ j, volume (I j) ≤ ENNReal.ofReal (s j))
    (hcover : uIcc a b ⊆ E ∪ N ∪ ⋃ j, I j) : |b-a| ≤ C+∑' j, s j := by
  have h := interval_length_le_image_and_tolls hN hcover
  have hb : ENNReal.ofReal |b-a| ≤ ENNReal.ofReal (C+∑' j, s j) := by
    apply h.trans
    calc
      volume E + ∑' j, volume (I j) ≤ ENNReal.ofReal C + ∑' j, ENNReal.ofReal (s j) :=
        add_le_add hE (ENNReal.tsum_le_tsum hI)
      _ = ENNReal.ofReal C + ENNReal.ofReal (∑' j, s j) := by rw [ENNReal.ofReal_tsum_of_nonneg hs hsum]
      _ = _ := (ENNReal.ofReal_add hC (tsum_nonneg hs)).symm
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hC (tsum_nonneg hs))).mp hb

end CircleDomainRigidity

end

end OAI
