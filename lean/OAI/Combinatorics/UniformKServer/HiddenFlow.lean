import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalRanks
import OAI.Combinatorics.UniformKServer.PilotEdits

namespace OAI

                                 
section

/-! The true-metric posterior flow is derived from literal labeled one-server
trajectories. Observing further partition randomness may refine the filtration;
no filtering identity on a later selected event is assumed. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

structure Data (X Ω : Type*) [Fintype Ω] (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  position : ℕ → Ω → Fin k → X
  chosen : ℕ → Ω → Fin k
  request : ℕ → Ω → X
  update : ∀ t ω a, position (t+1) ω a=if a=chosen t ω then request t ω else position t ω a
  request_measurable : ∀ t ω v, (filtration (t+1)).r ω v → request t ω=request t v

def atom (x y : X) : ℝ := if x=y then 1 else 0

def counts (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  ∑ a : Fin k, atom (D.position t ω a) y

def moverAtom (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  atom (D.position t ω (D.chosen t ω)) y

def current (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration t) (fun v => counts D t v y) ω

def filtered (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration (t+1)) (fun v => counts D t v y) ω

def mover (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : ℝ :=
  posterior D.weight (D.filtration (t+1)) (fun v => moverAtom D t v y) ω

omit [Fintype X] in
theorem atom_nonneg (x y : X) : 0 ≤ atom x y := by unfold atom; split_ifs <;> norm_num

theorem atom_total (x : X) : (∑ y, atom x y)=1 := by simp [atom]

omit [Fintype X] in
theorem counts_nonneg (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) : 0 ≤ counts D t ω y :=
  sum_nonneg fun _ _ => atom_nonneg _ _

theorem counts_total (D : Data X Ω k) (t : ℕ) (ω : Ω) : (∑ y, counts D t ω y)=k := by
  unfold counts
  rw [sum_comm]
  simp only [atom_total,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

omit [Fintype X] in
theorem mover_le_count (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) :
    moverAtom D t ω y ≤ counts D t ω y :=
  single_le_sum (fun a _ => atom_nonneg (D.position t ω a) y) (mem_univ (D.chosen t ω))

omit [Fintype X] in
theorem counts_update (D : Data X Ω k) (t : ℕ) (ω : Ω) (y : X) :
    counts D (t+1) ω y=counts D t ω y-moverAtom D t ω y+atom (D.request t ω) y := by
  have he (a : Fin k) : atom (D.position (t+1) ω a) y=atom (D.position t ω a) y+
      if a=D.chosen t ω then atom (D.request t ω) y-atom (D.position t ω a) y else 0 := by
    rw [D.update]
    split_ifs <;> ring
  simp only [counts,he,sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true,moverAtom]
  ring

omit [Fintype X] in
theorem normalization (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    (∑ v, kernel D.weight (D.filtration t) ω v)=1 := by
  apply ConditionalRanks.normalized_kernel
  exact ne_of_gt (lt_of_lt_of_le (D.positive ω)
    (weight_le_mass (fun v => (D.positive v).le) _ _))

omit [Fintype X] in
theorem posterior_local (D : Data X Ω k) (t : ℕ) (ω : Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ v, (D.filtration t).r ω v → f v=c) :
    posterior D.weight (D.filtration t) f ω=c := by
  unfold posterior
  calc
    _ = ∑ v, kernel D.weight (D.filtration t) ω v*c := by
      apply sum_congr rfl
      intro v _
      by_cases h : (D.filtration t).r ω v
      · rw [hf v h]
      · simp only [kernel,ite_eq_right h,zero_mul]
    _ = _ := by rw [←sum_mul,normalization,one_mul]

theorem posterior_total (D : Data X Ω k) (t : ℕ) (ω : Ω) (f : Ω → X → ℝ) (c : ℝ)
    (hf : ∀ v, ∑ y, f v y=c) :
    (∑ y, posterior D.weight (D.filtration t) (fun v => f v y) ω)=c := by
  unfold posterior
  rw [sum_comm]
  simp only [←mul_sum,hf,←sum_mul,normalization,one_mul]

omit [Fintype X] in
theorem posterior_mono (D : Data X Ω k) (t : ℕ) (ω : Ω) (f g : Ω → ℝ)
    (hfg : ∀ v, f v ≤ g v) :
    posterior D.weight (D.filtration t) f ω ≤ posterior D.weight (D.filtration t) g ω :=
  sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hfg v) (kernel_nonneg (fun v => (D.positive v).le) _ _ _)

def flow (D : Data X Ω k) : PilotEdits.Flow X Ω k where
  weight := D.weight
  weight_nonneg := fun ω => (D.positive ω).le
  weight_total := D.total
  filtration := D.filtration
  refines := D.refines
  post := current D
  filtered := filtered D
  mover := mover D
  request := D.request
  post_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => counts_nonneg D t v y) _ _
  post_total := fun t ω => posterior_total D t ω (fun v y => counts D t v y) k (counts_total D t)
  filtered_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => counts_nonneg D t v y) _ _
  filtered_total := fun t ω => posterior_total D (t+1) ω (fun v y => counts D t v y) k (counts_total D t)
  mover_nonneg := fun t ω y => posterior_nonneg (fun v => (D.positive v).le) (fun v => atom_nonneg _ _) _ _
  mover_total := fun t ω => posterior_total D (t+1) ω (fun v y => moverAtom D t v y) 1 (fun v => atom_total _)
  mover_le := fun t ω y => posterior_mono D (t+1) ω _ _ (fun v => mover_le_count D t v y)
  update := by
    intro t ω y
    have hd := posterior_local D (t+1) ω (fun v => atom (D.request t v) y) (atom (D.request t ω) y)
      (fun v hv => by rw [D.request_measurable t ω v hv])
    unfold current filtered mover posterior at *
    simp only [counts_update,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
    rw [hd]
    simp only [atom,eq_comm]
  post_measurable := by
    intro t ω v h
    funext y
    exact posterior_measurable _ _ _ ω v h
  filtering := by
    intro t b hb y
    exact ConditionalLaw.filtering (fun v => (D.positive v).le) (D.filtration t) (D.filtration (t+1))
      (D.refines t) b (fun v => counts D t v y) hb

section Cost
variable [MetricSpace X]

theorem expected_mover_cost (D : Data X Ω k) (t : ℕ) :
    (∑ ω, D.weight ω*PilotEdits.moverCost (flow D) t ω)=
    ∑ ω, D.weight ω*dist (D.request t ω) (D.position t ω (D.chosen t ω)) := by
  unfold PilotEdits.moverCost
  change (∑ ω, D.weight ω*∑ y, mover D t ω y*dist (D.request t ω) y)=_
  simp only [mul_sum]
  rw [sum_comm]
  have he (y : X) : (∑ ω, D.weight ω*(mover D t ω y*dist (D.request t ω) y))=
      ∑ ω, D.weight ω*(moverAtom D t ω y*dist (D.request t ω) y) := by
    have h := test_identity (fun v => (D.positive v).le) (D.filtration (t+1))
      (fun v => dist (D.request t v) y) (fun v => moverAtom D t v y)
      (fun ω v hv => by change dist (D.request t ω) y=dist (D.request t v) y; rw [D.request_measurable t ω v hv])
    unfold mover
    convert h using 1 <;> apply sum_congr rfl <;> intro ω _ <;> ring
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  simp only [moverAtom,atom,ite_mul,one_mul,zero_mul]
  simp

end Cost
end UniformKServer.HiddenFlow

end


end

end OAI
