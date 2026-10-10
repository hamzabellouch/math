import Mathlib
import OAI.Combinatorics.KMedian.Optimization.SimplexProjection

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ} [NeZero n]

abbrev point (v : Vector ℚ n) : Fin n → ℚ := fun i => v[i.val]

def sqdist (x y : Fin n → ℚ) : ℚ := ∑ i, (x i-y i)^2

omit [NeZero n] in
theorem sqdist_nonneg (x y : Fin n → ℚ) : 0 ≤ sqdist x y :=
  sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero n] in
@[simp] theorem point_ofFn (f : Fin n → ℚ) : point (Vector.ofFn f)=f := by
  funext i
  simp only [point,Vector.getElem_ofFn]

omit [NeZero n] in
@[simp] theorem point_ofFn_apply (f : Fin n → ℚ) (i : Fin n) : point (Vector.ofFn f) i=f i := by
  simp only [point,Vector.getElem_ofFn]

def next (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ) (v : Vector ℚ n) : Vector ℚ n :=
  let w := Vector.ofFn (fun i => point v i-η*g (point v) i)
  let L := Simplex.level (point w) k
  Vector.ofFn (fun i => max 0 (point w i-L))

@[simp] theorem next_apply (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (i : Fin n) :
    point (next k η g v) i=Simplex.project (fun a => point v a-η*g (point v) a) k i := by
  simp only [next,point_ofFn_apply,point_ofFn,Simplex.project]

def trajectory (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : ℕ → Vector ℚ n
  | 0 => v
  | t+1 => next k η g (trajectory k η g v t)

@[simp] theorem trajectory_zero (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : trajectory k η g v 0=v := rfl

@[simp] theorem trajectory_succ (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (t : ℕ) :
    trajectory k η g v (t+1)=next k η g (trajectory k η g v t) := rfl

def feasible (k : ℚ) (x : Fin n → ℚ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i=k

theorem trajectory_feasible (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (hk : 0 < k) (hv : feasible k (point v)) (t : ℕ) :
    feasible k (point (trajectory k η g v t)) := by
  cases t with
  | zero => exact hv
  | succ t =>
    constructor
    · intro i; rw [trajectory_succ,next_apply]; exact Simplex.project_nonneg _ _ _
    · simp only [trajectory_succ,next_apply]
      exact Simplex.project_sum _ _ hk

theorem next_descent (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G : ℚ) (hk : 0 < k) (hη : 0 ≤ η)
    (v : Vector ℚ n) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : f (point v)-f z ≤ ∑ i, g (point v) i*(point v i-z i))
    (hg : ∑ i, (g (point v) i)^2 ≤ G) :
    sqdist (point (next k η g v)) z ≤
      sqdist (point v) z-2*η*(f (point v)-f z)+η^2*G := by
  have hp := Simplex.project_sqdist (fun i => point v i-η*g (point v) i) z k hk hz.1 hz.2
  have hid : (∑ i, (point v i-η*g (point v) i-z i)^2)=
      sqdist (point v) z-2*η*(∑ i, g (point v) i*(point v i-z i))+
        η^2*(∑ i, (g (point v) i)^2) := by
    unfold sqdist
    rw [mul_sum,mul_sum,← sum_sub_distrib,← sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [hid] at hp
  have hsg' := mul_le_mul_of_nonneg_left hsg (mul_nonneg (show (0:ℚ) ≤ 2 by norm_num) hη)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg η)
  have hmain : (∑ i, (Simplex.project (fun i => point v i-η*g (point v) i) k i-z i)^2) ≤
      sqdist (point v) z-2*η*(f (point v)-f z)+η^2*G := hp.trans (by linarith)
  simpa only [sqdist,next_apply] using hmain

theorem regret (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G : ℚ) (hk : 0 < k) (hη : 0 ≤ η) (v : Vector ℚ n)
    (hv : feasible k (point v)) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : ∀ y, feasible k y → f y-f z ≤ ∑ i, g y i*(y i-z i))
    (hg : ∀ y, feasible k y → ∑ i, (g y i)^2 ≤ G) (T : ℕ) :
    2*η*(∑ t ∈ range T, (f (point (trajectory k η g v t))-f z)) ≤
      sqdist (point v) z-sqdist (point (trajectory k η g v T)) z+(T:ℚ)*η^2*G := by
  induction T with
  | zero => simp only [range_zero,sum_empty,mul_zero,trajectory_zero,sub_self,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ T ih =>
    have ht := trajectory_feasible k η g v hk hv T
    have hd := next_descent f g k η G hk hη (trajectory k η g v T) z hz
      (hsg _ ht) (hg _ ht)
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one,trajectory_succ]
    linarith

theorem exists_accurate (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G δ : ℚ) (hk : 0 < k) (hη : 0 < η) (v : Vector ℚ n)
    (hv : feasible k (point v)) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : ∀ y, feasible k y → f y-f z ≤ ∑ i, g y i*(y i-z i))
    (hg : ∀ y, feasible k y → ∑ i, (g y i)^2 ≤ G) (T : ℕ) (hT : 0 < T)
    (hiter : sqdist (point v) z+(T:ℚ)*η^2*G ≤ 2*η*(T:ℚ)*δ) :
    ∃ t ∈ range T, f (point (trajectory k η g v t)) ≤ f z+δ := by
  by_contra hn
  push Not at hn
  have hsum : (T:ℚ)*δ < ∑ t ∈ range T, (f (point (trajectory k η g v t))-f z) := by
    calc
      _ = ∑ _t ∈ range T, δ := by simp only [sum_const,card_range,nsmul_eq_mul]
      _ < _ := sum_lt_sum (fun t ht => by linarith [hn t ht])
        ⟨0,mem_range.mpr hT,by linarith [hn 0 (mem_range.mpr hT)]⟩
  have hr := regret f g k η G hk hη.le v hv z hz hsg hg T
  have hd := sqdist_nonneg (point (trajectory k η g v T)) z
  have hh := mul_lt_mul_of_pos_left hsum (mul_pos (show (0:ℚ) < 2 by norm_num) hη)
  nlinarith

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
