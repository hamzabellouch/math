import Mathlib
import OAI.Combinatorics.UniformKServer.Fallback
import OAI.Combinatorics.UniformKServer.StarLocalCharges

namespace OAI

                                 
section

/-! The sole law-dependent energy is the actual hidden child-count movement.
Posterior drift is derived by conditional contraction, never assumed. -/
noncomputable section
namespace UniformKServer.StarEnergy
open Finset StarRanks RankTracking CoarseData StarLocalCharges
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def integral (d : Data Ω ι k) (H : ℕ) (f : ℕ → Ω → ℝ) : ℝ :=
  ∑ t ∈ range H, average d.weight (f t)

theorem integral_mono (d : Data Ω ι k) (H : ℕ) {f g : ℕ → Ω → ℝ}
    (h : ∀ t ω, f t ω ≤ g t ω) : integral d H f ≤ integral d H g :=
  sum_le_sum fun t _ => average_mono (fun ω => (d.positive ω).le) (h t)

theorem integral_nonneg (d : Data Ω ι k) (H : ℕ) {f : ℕ → Ω → ℝ}
    (h : ∀ t ω, 0 ≤ f t ω) : 0 ≤ integral d H f :=
  sum_nonneg fun t _ => sum_nonneg fun ω _ => mul_nonneg (d.positive ω).le (h t ω)

theorem integral_add (d : Data Ω ι k) (H : ℕ) (f g : ℕ → Ω → ℝ) :
    integral d H (fun t ω => f t ω+g t ω)=integral d H f+integral d H g := by
  simp only [integral,average_add,sum_add_distrib]

theorem integral_mul (d : Data Ω ι k) (H : ℕ) (f : ℕ → Ω → ℝ) (c : ℝ) :
    integral d H (fun t ω => c*f t ω)=c*integral d H f := by
  simp only [integral,average_mul,←mul_sum]

theorem integral_sum {A : Type*} [Fintype A] (d : Data Ω ι k) (H : ℕ) (f : A → ℕ → Ω → ℝ) :
    integral d H (fun t ω => ∑ a, f a t ω)=∑ a, integral d H (f a) := by
  simp only [integral,average_sum]
  exact sum_comm

def countMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, |(d.count (t+1) ω i:ℝ)-d.count t ω i|
def cost (d : Data Ω ι k) (H : ℕ) : ℝ := integral d H (countMove d)
def allowance (ι : Type*) [Fintype ι] (k : ℕ) : ℝ := (Fintype.card ι+1:ℝ)*(k+1)
def energy (d : Data Ω ι k) (H : ℕ) : ℝ := cost d H+allowance ι k

theorem cost_nonneg (d : Data Ω ι k) (H : ℕ) : 0 ≤ cost d H :=
  integral_nonneg d H fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem allowance_bounds (ι : Type*) [Fintype ι] (k : ℕ) :
    0 ≤ allowance ι k ∧ (k:ℝ) ≤ allowance ι k ∧ (Fintype.card ι:ℝ) ≤ allowance ι k ∧
    (Fintype.card ι:ℝ)*k ≤ allowance ι k := by
  have hk := Nat.cast_nonneg (α:=ℝ) k
  have hi := Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)
  unfold allowance
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem energy_nonneg (d : Data Ω ι k) (H : ℕ) : 0 ≤ energy d H :=
  add_nonneg (cost_nonneg d H) (allowance_bounds ι k).1

theorem cost_le_energy (d : Data Ω ι k) (H : ℕ) : cost d H ≤ energy d H :=
  le_add_of_nonneg_right (allowance_bounds ι k).1

theorem allowance_le_energy (d : Data Ω ι k) (H : ℕ) : allowance ι k ≤ energy d H :=
  le_add_of_nonneg_left (cost_nonneg d H)

theorem rank_drift (d : Data Ω ι k) (H : ℕ) (N : ℕ → Ω → ℕ) (hN : ∀ t ω, N t ω ≤ k) :
    totalDrift (fun j : Fin k => ConditionalRank.input d.weight (fun ω => (d.positive ω).le) d.total
      d.filtration d.refines N j) H ≤ integral d H (fun t ω => |(N (t+1) ω:ℝ)-N t ω|) := by
  unfold totalDrift driftBudget integral
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  simp only [ConditionalRank.input,Nat.add_sub_cancel,average]
  have h := ConditionalRank.total_drift (fun ω => (d.positive ω).le) (d.filtration (t+1))
    (N (t+1)) (N t) k (hN (t+1)) (hN t)
  simpa only [←Fin.sum_univ_eq_sum_range] using h

theorem child_drift (d : Data Ω ι k) (H : ℕ) :
    (∑ i, totalDrift (input d i) H) ≤ cost d H := by
  have h := sum_le_sum (s:=univ) fun i _ => rank_drift d H (fun t ω => d.count t ω i)
    (fun t ω => child_bound d t ω i)
  rw [←integral_sum] at h
  exact h

theorem parent_drift (d : Data Ω ι k) (H : ℕ) :
    totalDrift (parentInput d) H ≤ cost d H := by
  apply (rank_drift d H (fun t ω => ∑ i, d.count t ω i) d.bound).trans
  apply integral_mono
  intro t ω
  simp only [Nat.cast_sum]
  change |(∑ i, (d.count (t+1) ω i:ℝ))-(∑ i, (d.count t ω i:ℝ))| ≤ _
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem hidden_move (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ ir : ι × Fin k, |(StarOutputData.alphaData d).hidden (t+1) ω ir-
      (StarOutputData.alphaData d).hidden t ω ir|)=countMove d t ω := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  change (∑ j : Fin k, |ConditionalRank.indicator (d.count (t+1) ω i) j-
    ConditionalRank.indicator (d.count t ω i) j|)=_
  have h := ConditionalRank.indicator_distance (child_bound d (t+1) ω i) (child_bound d t ω i)
  simpa only [←Fin.sum_univ_eq_sum_range] using h

end UniformKServer.StarEnergy

end


end

end OAI
