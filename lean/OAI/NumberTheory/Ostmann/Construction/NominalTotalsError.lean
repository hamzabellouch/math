import OAI.NumberTheory.Ostmann.Construction.NominalTotals

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators Topology

def nominalGapMagnitude (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  |Conclusion.initialGap Bs k L|+∑j∈Finset.range k,|Conclusion.stepGap BD Bz k L j|

def nominalGapCoefficient (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  |Bs+8*Real.log (Conclusion.bulkScale k)|+
    ∑j∈Finset.range k,|(2:ℝ)^j*(BD+Bz*Real.log (Conclusion.bulkScale k)+(2/5:ℝ)*Real.log ((2:ℝ)^j))|

theorem nominalGapMagnitude_eq (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) :
    nominalGapMagnitude Bs BD Bz k L = nominalGapCoefficient Bs BD Bz k*(Conclusion.bulkSize k L:ℝ) := by
  unfold nominalGapMagnitude nominalGapCoefficient Conclusion.initialGap Conclusion.stepGap
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Conclusion.bulkSize k L))]
  rw [← Finset.sum_mul,← add_mul]

theorem nominalGapMagnitude_eventually (Bs BD Bz : ℝ) (k : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, nominalGapMagnitude Bs BD Bz k L≤ε*favorableBlockWidth L := by
  let C := nominalGapCoefficient Bs BD Bz k
  have hC : 0≤C := by unfold C nominalGapCoefficient; positivity
  have hr : ∀ᶠ L : ℝ in atTop, C*Conclusion.bulkScale k/ε≤favorableBlockWidth L/L := by
    simpa only [Real.rpow_one,favorableBlockWidth] using
      (tendsto_exp_mul_div_rpow_atTop 1 (1/100) (by norm_num)).eventually_ge_atTop
        (C*Conclusion.bulkScale k/ε)
  filter_upwards [hr,eventually_ge_atTop (1:ℝ)] with L hr hL
  have hLp : 0<L := by linarith
  have hm := (Conclusion.bulkSize_bounds k hLp.le).2
  have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hLp).mp hr) hε.le
  have he : ε*(C*Conclusion.bulkScale k/ε*L)=C*(Conclusion.bulkScale k*L) := by field_simp
  rw [he] at hh
  rw [nominalGapMagnitude_eq]
  exact (mul_le_mul_of_nonneg_left hm hC).trans hh

theorem nominalWeight_error_eq {k j : ℕ} (hj : j<k) (J : ℝ) (Δ : ℕ → ℝ) :
    nominalWeight k J Δ j-(2:ℝ)^(k-1-j)*J =
      -(Δ j+∑i∈Finset.Ico j k,Δ i)/(2:ℝ)^(j+1) := by
  have he : (2:ℝ)^k=(2:ℝ)^(k-1-j)*(2:ℝ)^(j+1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold nominalWeight nominalTail
  rw [Finset.sum_eq_sum_Ico_succ_bot hj Δ,he,pow_succ]
  field_simp
  ring

theorem nominalWeight_error_le {k j : ℕ} (hj : j<k) (J : ℝ) (Δ : ℕ → ℝ) :
    |nominalWeight k J Δ j-(2:ℝ)^(k-1-j)*J| ≤ ∑i∈Finset.range k,|Δ i| := by
  let D := ∑i∈Finset.range k,|Δ i|
  have hD : 0≤D := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hjD : |Δ j|≤D := Finset.single_le_sum (f := fun i => |Δ i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hj)
  have hsub : (∑i∈Finset.Ico j k,|Δ i|)≤D :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
      (fun _ _ _ => abs_nonneg _)
  have hs : |∑i∈Finset.Ico j k,Δ i|≤D := (Finset.abs_sum_le_sum_abs _ _).trans hsub
  have hp : (2:ℝ)≤(2:ℝ)^(j+1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := j)]
  rw [nominalWeight_error_eq hj,abs_div,abs_neg,abs_of_pos (by positivity : (0:ℝ)<2^(j+1))]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^(j+1))).mpr
  calc
    _ ≤ |Δ j|+|∑i∈Finset.Ico j k,Δ i| := abs_add_le _ _
    _ ≤ D+D := add_le_add hjD hs
    _ ≤ _ := by nlinarith

theorem nominalCompensation_error_eventually (Bs BD Bz : ℝ) (k : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c td : ℝ, ∀ j<k,
      |nominalCompensation Bs BD Bz k L G₀ c td j-
        (2:ℝ)^(k-1-j)*nominalJ Bs BD Bz k L G₀ c td|≤ε*favorableBlockWidth L := by
  filter_upwards [nominalGapMagnitude_eventually Bs BD Bz k hε] with L hL
  intro G₀ c td j hj
  apply (nominalWeight_error_le hj _ _).trans
  apply le_trans _ hL
  unfold nominalGapMagnitude
  exact le_add_of_nonneg_left (abs_nonneg _)

end Ostmann.Construction

end

end OAI
