import Mathlib
import OAI.Combinatorics.KMedian.Optimization.SimplexDiameter
import OAI.Combinatorics.KMedian.Optimization.ComputedNearest
import OAI.Combinatorics.KMedian.Optimization.TruncatedObjective

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def gradSize (H : ℕ) : ℕ := n*(m*H)^2

def steps (r k H : ℕ) : ℕ := 8*r^2*(gradSize (n:=n) (m:=m) H)*k^2

def rate (r H : ℕ) : ℚ := 1/(2*(r:ℚ)*(gradSize (n:=n) (m:=m) H:ℚ))

theorem gradSize_pos (H : ℕ) (hH : 0 < H) : 0 < gradSize (n:=n) (m:=m) H := by
  unfold gradSize
  exact Nat.mul_pos (NeZero.pos n) (pow_pos (Nat.mul_pos (NeZero.pos m) hH) _)

theorem steps_pos (r k H : ℕ) (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) :
    0 < steps (n:=n) (m:=m) r k H := by
  unfold steps
  have hg := gradSize_pos (n:=n) (m:=m) H hH
  positivity

theorem rate_pos (r H : ℕ) (hr : 0 < r) (hH : 0 < H) :
    0 < rate (n:=n) (m:=m) r H := by
  unfold rate
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hr))
    (by exact_mod_cast gradSize_pos (n:=n) (m:=m) H hH))

theorem iteration_bound (r k H : ℕ) (hr : 0 < r) (hH : 0 < H)
    (v : Vector ℚ n) (z : Fin n → ℚ)
    (hv : feasible (k:ℚ) (point v)) (hz : feasible (k:ℚ) z) :
    sqdist (point v) z+(steps (n:=n) (m:=m) r k H:ℚ)*(rate (n:=n) (m:=m) r H)^2*
      (gradSize (n:=n) (m:=m) H:ℚ) ≤
      2*rate (n:=n) (m:=m) r H*(steps (n:=n) (m:=m) r k H:ℚ)*(1/(r:ℚ)) := by
  have hD := diameter_sq (k:ℚ) (point v) z hv hz
  have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hg0 : (gradSize (n:=n) (m:=m) H:ℚ) ≠ 0 := by
    exact_mod_cast (gradSize_pos (n:=n) (m:=m) H hH).ne'
  have hsteps : (steps (n:=n) (m:=m) r k H:ℚ)=
      8*(r:ℚ)^2*(gradSize (n:=n) (m:=m) H:ℚ)*(k:ℚ)^2 := by
    simp only [steps,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hnoise : (steps (n:=n) (m:=m) r k H:ℚ)*(rate (n:=n) (m:=m) r H)^2*
      (gradSize (n:=n) (m:=m) H:ℚ)=2*(k:ℚ)^2 := by
    rw [hsteps,rate]
    field_simp
    ring
  have hgain : 2*rate (n:=n) (m:=m) r H*(steps (n:=n) (m:=m) r k H:ℚ)*(1/(r:ℚ))=
      8*(k:ℚ)^2 := by
    rw [hsteps,rate]
    field_simp
  rw [hnoise,hgain]
  nlinarith [sq_nonneg (k:ℚ)]

def optimize (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) : Vector ℚ n :=
  let T := steps (n:=n) (m:=m) r k H
  letI : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  v a.val

theorem optimize_spec (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) (hd : ∀ j i, 0 ≤ d j i)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z) :
    feasible (k:ℚ) (point (optimize d r k H hr hk hH)) ∧
      objective d (point (optimize d r k H hr hk hH)) H ≤ objective d z H+1/(r:ℚ) := by
  let T := steps (n:=n) (m:=m) r k H
  let : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  have hkq : (0:ℚ) < k := by exact_mod_cast hk
  have hHq : (1:ℚ) ≤ H := by exact_mod_cast hH
  have hstart := initial_feasible (n:=n) (k:ℚ) hkq.le
  have hh := Preparation.firstNearest_spec (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  change feasible (k:ℚ) (point (v a.val)) ∧
    objective d (point (v a.val)) H ≤ objective d z H+1/(r:ℚ)
  refine ⟨trajectory_feasible _ _ _ _ hkq hstart _,?_⟩
  obtain ⟨t,ht,htc⟩ := exists_accurate (fun y => objective d y H) (fun y => gradient d y H)
    (k:ℚ) (rate (n:=n) (m:=m) r H) (gradSize (n:=n) (m:=m) H:ℚ) (1/(r:ℚ))
    hkq (rate_pos r H hr hH) (initial (k:ℚ)) hstart z hz
    (fun y _ => subgradient d y z H)
    (fun y _ => by
      simpa only [gradSize,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using
        gradient_sq_bound d y H hHq hd)
    T (steps_pos r k H hr hk hH) (iteration_bound r k H hr hH _ z hstart hz)
  exact (hh.2 ⟨t,mem_range.mp ht⟩ (mem_univ _)).trans htc

end MetricKMedian.TruncatedLP
end
end

end OAI
