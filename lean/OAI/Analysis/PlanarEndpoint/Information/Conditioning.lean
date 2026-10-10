import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {V W Y : Type*} [Fintype V] [Fintype W] [Fintype Y]

def totalMass (q : V → Y → ℝ) : ℝ := ∑ v, rowMass q v

lemma rowMass_le_totalMass (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (v : V) :
    rowMass q v ≤ totalMass q :=
  Finset.single_le_sum (fun b _ => rowMass_nonneg q hq b) (Finset.mem_univ v)

lemma totalMass_nonneg (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) :
    0 ≤ totalMass q := Finset.sum_nonneg (fun v _ => rowMass_nonneg q hq v)

lemma colMass_sum (q : V → Y → ℝ) : (∑ y, colMass q y) = totalMass q := by
  unfold colMass totalMass rowMass
  rw [Finset.sum_comm]

lemma joint_conditioning_exception_le_mass (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) {L η : ℝ} (hL : 1 < L) :
    (∑ v, ∑ y, if information L (colMass q y / totalMass q) -
        information L (conditionalMass q v y) < -η then q v y else 0) ≤
      L ^ (-η) * totalMass q := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hε : 0 ≤ L ^ (-η) := Real.rpow_nonneg hL0.le _
  have hp : ∀ y, 0 ≤ colMass q y / totalMass q :=
    fun y => div_nonneg (colMass_nonneg q hq y) (totalMass_nonneg q hq)
  calc
    _ ≤ ∑ v, ∑ y, L ^ (-η) * rowMass q v * (colMass q y / totalMass q) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro y _
      by_cases hzero : q v y = 0
      · simp only [hzero, ite_self]
        exact mul_nonneg (mul_nonneg hε (rowMass_nonneg q hq v)) (hp y)
      · have hqpos : 0 < q v y := lt_of_le_of_ne (hq v y) (Ne.symm hzero)
        have hvpos : 0 < rowMass q v := hqpos.trans_le (le_rowMass q hq v y)
        have hmpos : 0 < totalMass q := hvpos.trans_le (rowMass_le_totalMass q hq v)
        have hypos : 0 < colMass q y := hqpos.trans_le (le_colMass q hq v y)
        split_ifs with hbad
        · have h := (information_bad_iff hL (div_pos hypos hmpos)
            (div_pos hqpos hvpos)).mp hbad
          have h' := (div_lt_iff₀ hvpos).mp h
          nlinarith
        · exact mul_nonneg (mul_nonneg hε hvpos.le) (hp y)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_div, colMass_sum]
      by_cases hm : totalMass q = 0
      · simp [hm]
      · rw [div_self hm]
        simp_rw [mul_one]
        rw [← Finset.mul_sum]
        rfl

variable {S : Type*} [Fintype S]

lemma sampledTable_event_mass (a : S → ℝ) (v : S → V) (y : S → Y)
    (P : V → Y → Prop) :
    (∑ b, ∑ z, if P b z then sampledTable a v y b z else 0) =
      ∑ s, if P (v s) (y s) then a s else 0 := by
  calc
    _ = ∑ b, ∑ z, sampledTable a v y b z * (if P b z then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp
    _ = ∑ s, a s * (if P (v s) (y s) then (1 : ℝ) else 0) :=
      sampledTable_sum a v y (fun b z => if P b z then (1 : ℝ) else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp

omit [Fintype V] [Fintype Y] in
lemma sampledTable_pair_first (a : S → ℝ) (v : S → V) (u : S → W)
    (y : S → Y) (b : V) (z : Y) :
    (∑ c, sampledTable a (fun s => (v s, u s)) y (b,c) z) = sampledTable a v y b z := by
  unfold sampledTable
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hv : v s = b <;> by_cases hy : y s = z <;> simp [Prod.mk.injEq, hv, hy]

omit [Fintype V] in
lemma sampledTable_pair_total (a : S → ℝ) (v : S → V) (u : S → W)
    (y : S → Y) (b : V) :
    totalMass (fun c z => sampledTable a (fun s => (v s, u s)) y (b,c) z) =
      rowMass (sampledTable a v y) b := by
  unfold totalMass rowMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  exact sampledTable_pair_first a v u y b z

lemma sampled_conditioning_exception_le (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (u : S → W) (y : S → Y)
    {L η : ℝ} (hL : 1 < L) :
    (∑ s, if sampledInformation L a v y s -
        sampledInformation L a (fun s => (v s, u s)) y s < -η then a s else 0)
      ≤ L ^ (-η) := by
  let q : V → W → Y → ℝ := fun b c z =>
    sampledTable a (fun s => (v s, u s)) y (b,c) z
  let P : (V × W) → Y → Prop := fun b z =>
    information L (conditionalMass (sampledTable a v y) b.1 z) -
      information L (conditionalMass (sampledTable a (fun s => (v s, u s)) y) b z) < -η
  change (∑ s, if P (v s, u s) (y s) then a s else 0) ≤ _
  rw [← sampledTable_event_mass a (fun s => (v s, u s)) y P, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ b, L ^ (-η) * totalMass (q b) := by
      apply Finset.sum_le_sum
      intro b _
      have h := joint_conditioning_exception_le_mass (q b)
        (fun c z => sampledTable_nonneg a ha _ y (b,c) z) hL (η := η)
      have hcol : ∀ z, colMass (q b) z = sampledTable a v y b z :=
        sampledTable_pair_first a v u y b
      have ht : totalMass (q b) = rowMass (sampledTable a v y) b :=
        sampledTable_pair_total a v u y b
      simp_rw [hcol, ht] at h
      rw [ht]
      exact h
    _ = _ := by
      rw [← Finset.mul_sum]
      have ht : (∑ b, totalMass (q b)) = 1 := by
        simp only [q, sampledTable_pair_total, rowMass]
        rw [sampledTable_total, ha1]
      rw [ht, mul_one]

end PlanarEndpoint.TransverseInformation
end

end OAI
