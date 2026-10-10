import Mathlib
import OAI.Combinatorics.KMedian.Optimization.TruncatedOptimization
import OAI.Combinatorics.KMedian.Optimization.TruncatedRepair

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def penalty (r k : ℕ) : ℕ := 4*r*(k+1)

def loss (r k : ℕ) : ℚ := (1+1/(r:ℚ))/(penalty r k:ℚ)

theorem penalty_pos (r k : ℕ) (hr : 0 < r) : 0 < penalty r k := by
  unfold penalty
  positivity

theorem penalty_one (r k : ℕ) (hr : 0 < r) : (1:ℚ) ≤ penalty r k := by
  exact_mod_cast penalty_pos r k hr

theorem loss_bounds (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    0 < loss r k ∧ loss r k ≤ 1/(4*(r:ℚ)) ∧ loss r k < 1 ∧
      loss r k*((k:ℚ)+1) ≤ 1 := by
  have hrq : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hkq : (1:ℚ) ≤ k := by exact_mod_cast hk
  have hrp : (0:ℚ) < r := by linarith
  have hkp : (0:ℚ) < (k:ℚ)+1 := by linarith
  have ht : 1/(r:ℚ) ≤ 1 := (div_le_one hrp).mpr hrq
  have hH : (penalty r k:ℚ)=4*(r:ℚ)*((k:ℚ)+1) := by
    simp only [penalty,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  have hpos : 0 < loss r k := by
    unfold loss
    exact div_pos (by positivity) (by exact_mod_cast penalty_pos r k hr)
  have hb : loss r k ≤ 1/(4*(r:ℚ)) := by
    unfold loss
    rw [hH]
    apply (div_le_div_iff₀ (mul_pos (by positivity) hkp) (by positivity)).mpr
    nlinarith
  refine ⟨hpos,hb,?_,?_⟩
  · have hh : 1/(4*(r:ℚ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    exact hb.trans_lt hh
  · unfold loss
    rw [hH,div_mul_eq_mul_div]
    apply (div_le_one (by positivity)).mpr
    nlinarith

omit [NeZero n] [NeZero m] in
theorem repair_error (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (s : ℚ) (hs : 1/2 ≤ s) :
    (s+1/(r:ℚ))/(1-loss r k) ≤ (1+3/(r:ℚ))*s := by
  obtain ⟨_,hρ,hρ1,_⟩ := loss_bounds r k hr hk
  have hrq : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hrp : (0:ℚ) < r := by linarith
  let t : ℚ := 1/(r:ℚ)
  have ht : 0 ≤ t := le_of_lt (one_div_pos.mpr hrp)
  have ht1 : t ≤ 1 := (div_le_one hrp).mpr hrq
  have hρt : loss r k ≤ t/4 := by
    convert hρ using 1
    dsimp [t]
    ring
  have hp := mul_le_mul_of_nonneg_right hρt (by linarith : 0 ≤ 1+3*t)
  have hsq : t*t ≤ t := by nlinarith
  have hp' : loss r k*(1+3*t) ≤ t := by nlinarith
  have hs0 : 0 ≤ s := by linarith
  have hps := mul_le_mul_of_nonneg_right hp' hs0
  apply (div_le_iff₀ (sub_pos.mpr hρ1)).mpr
  have he : 3/(r:ℚ)=3*t := by dsimp [t]; ring
  rw [he]
  change s+t ≤ (1+3*t)*s*(1-loss r k)
  nlinarith [mul_nonneg ht (show 0 ≤ 2*s-1 by linarith)]

structure FractionalData (n m : ℕ) where
  opening : Vector ℚ n
  assignment : Vector (Vector ℚ n) m

def approximation (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hy : feasible (k:ℚ) y := (optimize_spec d r k H hr hk (penalty_pos r k hr) hd
    (point (initial (k:ℚ))) (initial_feasible _ (by positivity))).1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  ⟨Vector.ofFn (repairedOpening y (loss r k)),
    Vector.ofFn (fun j => Vector.ofFn (repairedAssignment d x j))⟩

theorem approximation_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (s : ℚ) (hs : 1/2 ≤ s) (hs1 : s ≤ 1)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z)
    (hzc : objective d z (penalty r k) ≤ s) :
    let a := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ a.opening[i.val] ∧ a.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ a.assignment[j.val][i.val] ∧
      a.assignment[j.val][i.val] ≤ a.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, a.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]*d j i) ≤ (1+3/(r:ℚ))*s := by
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hyc := optimize_spec d r k H hr hk (penalty_pos r k hr) hd z hz
  have hy : feasible (k:ℚ) y := hyc.1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  have hx := fun j => Preparation.computedNearest_spec y (truncated d H j) hy.1 hym H
  have hxe : (∑ j, ∑ i, x j i*truncated d H j i)=objective d y H := by
    exact sum_congr rfl (fun j _ => (hx j).2.2)
  have hc : (∑ j, ∑ i, x j i*truncated d H j i) ≤ s+1/(r:ℚ) := by
    rw [hxe]
    exact hyc.2.trans (by dsimp [H] at *; linarith)
  have hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ loss r k*(H:ℚ) := by
    have he : loss r k*(H:ℚ)=1+1/(r:ℚ) := by
      unfold loss
      exact div_mul_cancel₀ _ (by exact_mod_cast (penalty_pos r k hr).ne')
    rw [he]
    exact hc.trans (by linarith)
  obtain ⟨_,_,hρ,hkρ⟩ := loss_bounds r k hr hk
  obtain ⟨h1,h2,h3,h4,h5⟩ := repaired_spec d x y H (loss r k) k
    (penalty_one r k hr) hρ hkρ hd hy.1 (fun j => (hx j).1)
    (fun j => (hx j).2.1) hy.2.le hcost
  have hfinal := h5.trans ((div_le_div_of_nonneg_right hc (sub_pos.mpr hρ).le).trans
    (repair_error r k hr hk s hs))
  simpa only [approximation,Vector.getElem_ofFn] using And.intro h1 (And.intro h2
    (And.intro h3 (And.intro h4 hfinal)))

end MetricKMedian.TruncatedLP
end
end

end OAI
