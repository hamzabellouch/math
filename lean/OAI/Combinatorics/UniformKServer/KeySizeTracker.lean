import Mathlib
import OAI.Combinatorics.UniformKServer.RankTracking
import OAI.Combinatorics.UniformKServer.EntropyCredit

namespace OAI

                                     
section

/-! The unreset affine entropy tracker for each fixed heavy-key slot. Filtering
is charged at the old measurable coefficient on every step. -/
noncomputable section
namespace UniformKServer.KeySizeTracker
open Finset RankTracking EntropyCredit
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

structure Input (Ω : Type*) [Fintype Ω] (K : ℝ) where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  size : ℕ → Ω → ℝ
  filtered : ℕ → Ω → ℝ
  range : ∀ t ω, size t ω ∈ Set.Icc 1 K
  measurable : ∀ t, measurableAt filtration t (size t)
  filtering : ∀ t a, measurableAt filtration t a →
    average weight (fun ω => a ω*(filtered (t+1) ω-size t ω))=0

variable {K : ℝ}

def keep (s u : ℝ) : Prop := s ≤ (6/5)*u ∧ u ≤ (6/5)*s

def held (I : Input Ω K) : ℕ → Ω → ℝ
  | 0, ω => I.size 0 ω
  | t+1, ω => if keep (I.size (t+1) ω) (held I t ω) then held I t ω else I.size (t+1) ω

def charge (I : Input Ω K) (t : ℕ) (ω : Ω) : ℝ :=
  if keep (I.size (t+1) ω) (held I t ω) then 0 else held I t ω+held I (t+1) ω

def pot (I : Input Ω K) (t : ℕ) (ω : Ω) : ℝ := tangent (held I t ω) (I.size t ω)
def ell (K : ℝ) : ℝ := 1+Real.log K

theorem held_range (I : Input Ω K) (t : ℕ) (ω : Ω) : held I t ω ∈ Set.Icc 1 K := by
  induction t with
  | zero => exact I.range 0 ω
  | succ t ih => simp only [held]; split_ifs; exact ih; exact I.range _ _

theorem comparisons (I : Input Ω K) (t : ℕ) (ω : Ω) : keep (I.size t ω) (held I t ω) := by
  have hp := (I.range t ω).1
  cases t with
  | zero => simp only [held,keep]; constructor <;> nlinarith
  | succ t =>
    simp only [held]
    split_ifs with h
    · exact h
    · unfold keep; constructor <;> nlinarith

theorem held_measurable (I : Input Ω K) (t : ℕ) : measurableAt I.filtration t (held I t) := by
  induction t with
  | zero => exact I.measurable 0
  | succ t ih =>
    intro ω v hv
    have ho := ih ω v (I.refines t ω v hv)
    have hn := I.measurable (t+1) ω v hv
    simp only [held,ho,hn]

theorem slope_bound (K u : ℝ) (_hK : 1 ≤ K) (hu : u ∈ Set.Icc 1 K) :
    |-(1+Real.log u)| ≤ ell K := by
  have hup : 0 < u := by linarith [hu.1]
  have hl := Real.log_nonneg hu.1
  have hm := Real.log_le_log hup hu.2
  rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1+Real.log u)]
  unfold ell
  linarith

theorem potential_bound (I : Input Ω K) (hK : 1 ≤ K) (t : ℕ) (ω : Ω) :
    |pot I t ω| ≤ K*(1+ell K) := by
  have hu := held_range I t ω
  have hs := I.range t ω
  have he : |1+Real.log (held I t ω)| ≤ ell K := by simpa only [abs_neg] using slope_bound K _ hK hu
  have hp : 0 ≤ ell K := by unfold ell; linarith [Real.log_nonneg hK]
  unfold pot tangent
  calc
    _ ≤ |held I t ω|+|(1+Real.log (held I t ω))*I.size t ω| := abs_sub _ _
    _ = held I t ω+|1+Real.log (held I t ω)| *I.size t ω := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ held I t ω by linarith [hu.1]),
        abs_of_nonneg (show 0 ≤ I.size t ω by linarith [hs.1])]
    _ ≤ K+(ell K)*K := add_le_add hu.2 (mul_le_mul he hs.2 (by linarith [hs.1]) hp)
    _ = _ := by ring

theorem step_release (I : Input Ω K) (t : ℕ) (ω : Ω) :
    charge I t ω ≤ 144*(tangent (held I t ω) (I.size (t+1) ω)-pot I (t+1) ω) := by
  by_cases h : keep (I.size (t+1) ω) (held I t ω)
  · simp only [charge,pot,held,ite_eq_left h,sub_self,mul_zero,le_refl]
  · have hc := relative_credit (I.size (t+1) ω) (held I t ω)
      (by linarith [(I.range (t+1) ω).1]) (by linarith [(held_range I t ω).1]) h
    simpa only [charge,ite_eq_right h,pot,held,add_comm] using hc

theorem potential_step (I : Input Ω K) (t : ℕ) (ω : Ω) :
    charge I t ω+144*pot I (t+1) ω ≤ 144*pot I t ω+
      144*(-(1+Real.log (held I t ω)))*(I.filtered (t+1) ω-I.size t ω)+
      144*(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) := by
  have h := step_release I t ω
  simp only [pot,tangent] at *
  nlinarith only [h]

theorem expected_step (I : Input Ω K) (hK : 1 ≤ K) (t : ℕ) :
    average I.weight (charge I t)+144*average I.weight (pot I (t+1)) ≤
      144*average I.weight (pot I t)+144*ell K*
      average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|) := by
  have hf := I.filtering t (fun ω => 144*(-(1+Real.log (held I t ω)))) (by
    intro ω v hv
    dsimp only
    rw [held_measurable I t ω v hv])
  have hs := average_mono I.nonneg (potential_step I t)
  have he (ω : Ω) : 144*(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) ≤
      (144*ell K)*|I.size (t+1) ω-I.filtered (t+1) ω| := by
    have hl : (-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) ≤
        ell K*|I.size (t+1) ω-I.filtered (t+1) ω| := by
      calc
        _ ≤ |(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω)| := le_abs_self _
        _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (slope_bound K _ hK (held_range I t ω)) (abs_nonneg _)
    nlinarith
  have hb := average_mono I.nonneg he
  simp only [average_add,average_mul] at hs hb
  rw [hf] at hs
  linarith

theorem budget (I : Input Ω K) (hK : 1 ≤ K) (H : ℕ) :
    (∑ t ∈ Finset.range H, average I.weight (charge I t)) ≤
      144*ell K*(∑ t ∈ Finset.range H,
        average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|))+288*K*(1+ell K) := by
  have ht : ∀ H, (∑ t ∈ Finset.range H, average I.weight (charge I t))+
      144*average I.weight (pot I H) ≤
      144*ell K*(∑ t ∈ Finset.range H,
        average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|))+
          144*average I.weight (pot I 0) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      have hs := expected_step I hK H
      rw [sum_range_succ,sum_range_succ]
      linarith
  have hr (t : ℕ) : |average I.weight (pot I t)| ≤ K*(1+ell K) := by
    calc
      _ ≤ ∑ ω, |I.weight ω*pot I t ω| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω, I.weight ω*(K*(1+ell K)) := sum_le_sum fun ω _ => by
        rw [abs_mul,abs_of_nonneg (I.nonneg ω)]
        exact mul_le_mul_of_nonneg_left (potential_bound I hK t ω) (I.nonneg ω)
      _ = _ := by rw [←sum_mul,I.total,one_mul]
  have h0 := (abs_le.mp (hr 0)).2
  have hH := (abs_le.mp (hr H)).1
  nlinarith [ht H]

end UniformKServer.KeySizeTracker

end


end

end OAI
