import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetsBoundsBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceTargets
open scoped BigOperators

theorem pivotTarget_recurrence {k j : ℕ} (hj : j<k) (J : ℝ) (a Δ : ℕ→ℝ) :
    pivotTarget k J a Δ j=(2:ℝ)^j*J+
      (∑i∈Finset.Ico (j+1) k,pivotTarget k J a Δ i)+a j-Δ (j+1) := by
  unfold pivotTarget
  rw [target_recurrence hj,coefficient]
  ring

theorem targets_total_identity (k : ℕ) (logX J : ℝ) (a Δ : ℕ→ℝ) :
    2*(J+(∑j∈Finset.range k,(pivotTarget k J a Δ j+a j))+fillerTarget k logX J a Δ)=
      logX+Δ 0 := by
  unfold fillerTarget
  ring

theorem targets_bounds {k : ℕ} (hk : 0<k) {τ J logX : ℝ}
    (hτ : 0<τ) (hJlo : (9/10:ℝ)*τ≤J) (hJhi : J≤4*τ)
    (a Δ : ℕ→ℝ) (ha : ∀j<k,0≤a j ∧ a j≤4*τ)
    (hΔ : ∀i≤k,0≤Δ i ∧ Δ i≤τ/10)
    (hXlo : 999*(4:ℝ)^k*τ≤logX) (hXhi : logX≤1000*(4:ℝ)^k*τ) :
    (∀j<k,(1/10:ℝ)*(2:ℝ)^k*τ≤pivotTarget k J a Δ j ∧
      pivotTarget k J a Δ j≤600*(4:ℝ)^k*τ) ∧
    (1/10:ℝ)*(2:ℝ)^k*τ≤fillerTarget k logX J a Δ ∧
      fillerTarget k logX J a Δ≤600*(4:ℝ)^k*τ := by
  have hc : ∀i<k,0≤coefficient J a Δ i :=
    fun i hi=>coefficient_nonneg hτ.le hJlo a Δ (fun j hj=>(ha j hj).1)
      (fun i hi=>(hΔ i hi).2) hi
  have hT : ∀i<k,0≤pivotTarget k J a Δ i := fun i hi=>target_nonneg hi _ hc
  have hTsum : 0≤∑j∈Finset.range k,pivotTarget k J a Δ j :=
    Finset.sum_nonneg fun j hj=>hT j (Finset.mem_range.mp hj)
  have hTupper := pivotTarget_total_le hτ.le hJhi a Δ
    (fun j hj=>(ha j hj).2) (fun i hi=>(hΔ i hi).1)
  have hAsum : 0≤∑j∈Finset.range k,a j :=
    Finset.sum_nonneg fun j hj=>(ha j (Finset.mem_range.mp hj)).1
  have hAupper : (∑j∈Finset.range k,a j)≤4*(4:ℝ)^k*τ := by
    calc
      _ ≤ ∑_j∈Finset.range k,4*τ := Finset.sum_le_sum (fun j hj=>(ha j (Finset.mem_range.mp hj)).2)
      _ = (k:ℝ)*(4*τ) := by simp
      _ ≤ (4:ℝ)^k*(4*τ) := mul_le_mul_of_nonneg_right (cast_le_four_pow k) (by positivity)
      _ = _ := by ring
  have hp4 : (1:ℝ)≤4^k := one_le_pow₀ (by norm_num)
  have hτ4 : τ≤(4:ℝ)^k*τ := by simpa using mul_le_mul_of_nonneg_right hp4 hτ.le
  have hp24 : (2:ℝ)^k≤4^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hτ24 := mul_le_mul_of_nonneg_right hp24 hτ.le
  have hJ0 : 0≤J := by linarith
  have hΔ0 := hΔ 0 (Nat.zero_le k)
  have hfour : 0≤(4:ℝ)^k*τ := by positivity
  constructor
  · intro j hj
    refine ⟨pivotTarget_lower hk hj hτ.le hJlo a Δ (fun i hi=>(ha i hi).1)
      (fun i hi=>(hΔ i hi).2),?_⟩
    have ht : pivotTarget k J a Δ j≤∑i∈Finset.range k,pivotTarget k J a Δ i :=
      target_le_total hj _ hc
    linarith
  · unfold fillerTarget
    rw [Finset.sum_add_distrib]
    constructor <;> nlinarith

end Ostmann.Characters.HigherBiasSourceTargets

end

end OAI
