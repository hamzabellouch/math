import Mathlib
import OAI.Probability.SKSupport.Control.ControlledGrid

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma sum_range_blocks (f : ℕ → ℝ) (n m : ℕ) :
    ∑ j ∈ Finset.range (n*m), f j =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, f (k*m+j) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Nat.succ_mul, Finset.sum_range_add, IH, Finset.sum_range_succ]

omit mΩ in
lemma controlledGrid_formula (B : ℝ≥0 → Ω → ℝ) (α : ℝ≥0 → Ω → ℝ)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) (ω : Ω) :
    controlledGrid B α h c x n ω = x+B ((n:ℝ≥0)*h) ω-B 0 ω+
      ∑ k ∈ Finset.range n, stepDrift (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ω := by
  induction n with
  | zero => simp [controlledGrid]
  | succ n IH =>
    rw [controlledGrid, IH, Finset.sum_range_succ]
    ring

lemma stepDrift_subdivision {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (s h c : ℝ) (hh : 0 ≤ h) (m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range m, stepDrift α (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) c ω) =
      stepDrift α s h c ω := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hd : 0 ≤ h/(m:ℝ) := div_nonneg hh (Nat.cast_nonneg m)
  have hint : ∀ j < m, IntervalIntegrable (fun r => c*α r ω) volume
      (s+(j:ℝ)*(h/(m:ℝ))) (s+((j+1:ℕ):ℝ)*(h/(m:ℝ))) := by
    intro j hj
    convert (bounded_control_intervalIntegrable hm hb (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) hd ω).1.const_mul c using 1
    push_cast
    ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro j hj
    unfold stepDrift
    congr 1
    push_cast
    ring
  · unfold stepDrift
    congr 1
    · simp
    · field_simp

lemma stepCost_subdivision {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (s h c : ℝ) (hh : 0 ≤ h) (m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range m, stepCost α (s+(j:ℝ)*(h/(m:ℝ))) (h/(m:ℝ)) c ω) =
      stepCost α s h c ω := by
  have hsq : Measurable (fun p : ℝ × Ω => (α p.1 p.2)^2) := hm.pow_const 2
  have hb2 : ∀ r ω, |(α r ω)^2| ≤ 1 := fun r ω => by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hb r ω) 2
  have he := stepDrift_subdivision (α := fun r ω => (α r ω)^2) hsq hb2 s h c hh m hmpos ω
  unfold stepCost
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ => (1/2:ℝ)*z) he

lemma refined_time (h : ℝ≥0) {m : ℕ} (hm : 0 < m) (k j : ℕ) :
    ((k*m+j:ℕ):ℝ≥0)*(h/(m:ℝ≥0)) = (k:ℝ≥0)*h+(j:ℝ≥0)*(h/(m:ℝ≥0)) := by
  have hm0 : (m:ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

lemma refined_coefficient {m j : ℕ} (hm : 0 < m) (hj : j < m) (k : ℕ) :
    (k*m+j)/m = k := by
  rw [Nat.mul_comm k m, Nat.mul_add_div hm, Nat.div_eq_of_lt hj, Nat.add_zero]

lemma grid_drift_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range (n*m), stepDrift α ((j:ℝ≥0)*(h/(m:ℝ≥0))) (h/(m:ℝ≥0)) (c (j/m)) ω) =
      ∑ k ∈ Finset.range n, stepDrift α ((k:ℝ≥0)*h) h (c k) ω := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have ht (j : ℕ) : ((k*m+j:ℕ):ℝ)*(↑h/(↑m:ℝ)) =
      (k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ)) := by
    have he := congrArg NNReal.toReal (refined_time h hmpos k j)
    simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast] using he
  simp only [NNReal.coe_natCast]
  have he : (∑ j ∈ Finset.range m,
      stepDrift α (((k*m+j:ℕ):ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c ((k*m+j)/m)) ω) =
      ∑ j ∈ Finset.range m,
      stepDrift α ((k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c k) ω := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hmpos (Finset.mem_range.mp hj) k, ht j]
  rw [he]
  exact stepDrift_subdivision hm hb ((k:ℝ)*(h:ℝ)) h (c k) h.coe_nonneg m hmpos ω

lemma grid_cost_refinement {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (n m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    (∑ j ∈ Finset.range (n*m), stepCost α ((j:ℝ≥0)*(h/(m:ℝ≥0))) (h/(m:ℝ≥0)) (c (j/m)) ω) =
      ∑ k ∈ Finset.range n, stepCost α ((k:ℝ≥0)*h) h (c k) ω := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  have ht (j : ℕ) : ((k*m+j:ℕ):ℝ)*(↑h/(↑m:ℝ)) =
      (k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ)) := by
    have he := congrArg NNReal.toReal (refined_time h hmpos k j)
    simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast] using he
  simp only [NNReal.coe_natCast]
  have he : (∑ j ∈ Finset.range m,
      stepCost α (((k*m+j:ℕ):ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c ((k*m+j)/m)) ω) =
      ∑ j ∈ Finset.range m,
      stepCost α ((k:ℝ)*(h:ℝ)+(j:ℝ)*((h:ℝ)/(m:ℝ))) ((h:ℝ)/(m:ℝ)) (c k) ω := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [refined_coefficient hmpos (Finset.mem_range.mp hj) k, ht j]
  rw [he]
  exact stepCost_subdivision hm hb ((k:ℝ)*(h:ℝ)) h (c k) h.coe_nonneg m hmpos ω

lemma controlledGrid_refinement (B : ℝ≥0 → Ω → ℝ) {α : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hb : ∀ r ω, |α r ω| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n m : ℕ) (hmpos : 0 < m) (ω : Ω) :
    controlledGrid B α (h/(m:ℝ≥0)) (fun j => c (j/m)) x (n*m) ω =
      controlledGrid B α h c x n ω := by
  have hm' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    hm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have ht : ((n*m:ℕ):ℝ≥0)*(h/(m:ℝ≥0)) = (n:ℝ≥0)*h := by
    simpa using refined_time h hmpos n 0
  simp only [controlledGrid_formula]
  rw [ht]
  have he := grid_drift_refinement (α := fun r => α (Real.toNNReal r)) hm' (fun r ω => hb _ ω) h c n m hmpos ω
  simp only [NNReal.coe_div, NNReal.coe_natCast] at he ⊢
  rw [he]

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma refinement_successor {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (j+1)/m = j/m ∨ ((j+1)/m = j/m+1 ∧ j+1 = (j/m+1)*m) := by
  have hj := Nat.div_add_mod j m
  have hr := Nat.mod_lt j hm
  by_cases he : j%m+1 < m
  · left
    have hde : j+1 = m*(j/m)+(j%m+1) := by omega
    rw [hde, Nat.mul_add_div hm, Nat.div_eq_of_lt he, Nat.add_zero]
  · right
    have he' : j%m+1 = m := by omega
    have hde : j+1 = (j/m+1)*m := by
      calc j+1 = m*(j/m)+(j%m+1) := by omega
           _ = m*(j/m)+m := by rw [he']
           _ = (j/m+1)*m := by ring
    refine ⟨?_, hde⟩
    rw [hde, Nat.mul_comm, Nat.mul_div_cancel_left _ hm]

lemma refined_cell_subset (h : ℝ≥0) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Set.Icc ((j:ℝ)*((h:ℝ)/(m:ℝ))) (((j:ℝ)+1)*((h:ℝ)/(m:ℝ))) ⊆
      Set.Icc ((j/m:ℕ)*(h:ℝ)) (((j/m:ℕ)+1)*(h:ℝ)) := by
  have hd : 0 ≤ (h:ℝ)/(m:ℝ) := div_nonneg h.coe_nonneg (Nat.cast_nonneg m)
  have hl : j/m*m ≤ j := Nat.div_mul_le_self _ _
  have hu : j+1 ≤ (j/m+1)*m := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)
  have ht (k : ℕ) : ((k*m:ℕ):ℝ)*((h:ℝ)/(m:ℝ)) = (k:ℝ)*(h:ℝ) := by
    have he := congrArg NNReal.toReal (refined_time h hm k 0)
    simpa only [Nat.add_zero, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_natCast, Nat.cast_zero, zero_mul, add_zero] using he
  intro r hr
  constructor
  · calc (j/m:ℕ)*(h:ℝ) = ((j/m*m:ℕ):ℝ)*((h:ℝ)/(m:ℝ)) := (ht _).symm
         _ ≤ (j:ℝ)*((h:ℝ)/(m:ℝ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hd
         _ ≤ r := hr.1
  · calc r ≤ ((j:ℝ)+1)*((h:ℝ)/(m:ℝ)) := hr.2
         _ ≤ (((j/m+1)*m:ℕ):ℝ)*((h:ℝ)/(m:ℝ)) :=
           mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hd
         _ = ((j/m:ℕ)+1)*(h:ℝ) := by simpa only [Nat.cast_add, Nat.cast_one] using ht (j/m+1)

lemma verificationError_mono (c d C₂ D₂ C₃ D₃ L M h : ℝ≥0)
    (hc : c ≤ d) (h₂ : C₂ ≤ D₂) (h₃ : C₃ ≤ D₃) (hL : L ≤ M) :
    verificationError c C₂ C₃ L h ≤ verificationError d D₂ D₃ M h := by
  have hF := normalFirstMoment_nonneg
  have hT := normalThirdMoment_nonneg
  unfold verificationError
  gcongr

end ZeroTemperatureSK.WeakIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

end
end
end
end

end OAI
