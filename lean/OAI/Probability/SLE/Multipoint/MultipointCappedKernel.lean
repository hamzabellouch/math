import OAI.Probability.SLE.Multipoint.MultipointKernelGraph
import OAI.Probability.SLE.Multipoint.MultipointTupleNull

namespace OAI

/-! The exact fixed-cap, nearest-neighbor distance kernel from
`mp:kernel-integral`, and its expansion into finite graph terms. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

def capEntry {ι : Type*} [DecidableEq ι] (b : ℝ) (x : ι → ℂ) (i : ι) : Option ι → ℝ
  | none => b
  | some j => if j=i then b else dist (x i) (x j)

def cappedDistance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (x : ι → ℂ) (i : ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (capEntry b x i)

theorem cap_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ℝ} (hb : 0 < b) {x : ι → ℂ} (hx : Function.Injective x) (i : ι) :
    0 < cappedDistance b x i := by
  obtain ⟨o,_,ho⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (capEntry b x i)
  change 0 < Finset.univ.inf' Finset.univ_nonempty (capEntry b x i)
  rw [ho]
  cases o with
  | none => exact hb
  | some j =>
    dsimp only [capEntry]
    split_ifs with hji
    · exact hb
    · exact dist_pos.mpr (fun h => hji (hx h.symm))

theorem cap_le_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (x : ι → ℂ) (i : ι) : cappedDistance b x i ≤ b := by
  exact Finset.inf'_le (capEntry b x i) (Finset.mem_univ none)

theorem cap_le_dist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (x : ι → ℂ) (i j : ι) (hij : i≠j) :
    cappedDistance b x i ≤ dist (x i) (x j) := by
  change Finset.univ.inf' Finset.univ_nonempty (capEntry b x i) ≤ _
  have h := Finset.inf'_le (capEntry b x i) (Finset.mem_univ (some j))
  simpa only [capEntry,ite_eq_right hij.symm] using h

theorem continuous_cappedDistance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (i : ι) : Continuous (fun x : ι → ℂ => cappedDistance b x i) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro o _
  cases o with
  | none => exact continuous_const
  | some j =>
    dsimp only [capEntry]
    split_ifs
    · exact continuous_const
    · fun_prop

def cappedDistanceKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (cappedDistance b x i ^ (-α))

lemma measurable_cappedDistanceKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) : Measurable (cappedDistanceKernel (ι := ι) α b) := by
  apply Finset.measurable_prod
  intro i _
  exact (((continuous_cappedDistance b i).measurable.pow_const (-α)).ennreal_ofReal)

def rowChoice {ι : Type*} [DecidableEq ι] (α b : ℝ) (x : ι → ℂ) (i : ι) : Option ι → ℝ≥0∞
  | none => ENNReal.ofReal (b^(-α))
  | some j => if j=i then 0 else distanceKernel α (x i) (x j)

lemma cap_reciprocal_le_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) (i : ι) :
    ENNReal.ofReal (cappedDistance b x i ^ (-α)) ≤ ∑ o, rowChoice α b x i o := by
  obtain ⟨o,_,ho⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (capEntry b x i)
  change ENNReal.ofReal ((Finset.univ.inf' Finset.univ_nonempty (capEntry b x i))^(-α)) ≤ _
  rw [ho]
  cases o with
  | none =>
    exact Finset.single_le_sum (f := rowChoice α b x i)
      (fun _ _ => bot_le) (Finset.mem_univ none)
  | some j =>
    by_cases hji : j=i
    · simpa only [capEntry,ite_eq_left hji,rowChoice] using
        (Finset.single_le_sum (f := rowChoice α b x i) (fun _ _ => bot_le) (Finset.mem_univ none))
    · simpa only [capEntry,ite_eq_right hji,rowChoice,distanceKernel] using
        (Finset.single_le_sum (f := rowChoice α b x i) (fun _ _ => bot_le) (Finset.mem_univ (some j)))

lemma cappedDistanceKernel_le_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) :
    cappedDistanceKernel α b x ≤ ∑ f : ι → Option ι, ∏ i, rowChoice α b x i (f i) := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_le_prod (fun i _ => cap_reciprocal_le_row α b x i)

end SLEExactGauge.Multipoint

end

end OAI
