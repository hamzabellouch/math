import OAI.Combinatorics.ContingencyTables.Machines.GeometricRuntime
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # Expected time from geometrically accurate quadratic-cost prefixes -/

namespace ContingencyTables.QuadraticPrefixRuntime
open scoped BigOperators

lemma weighted_geometric : HasSum (fun k : ℕ => (2*(k:ℝ)+3)*(1/2:ℝ)^k) 10 := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)
  convert (h1.mul_left 2).add (h0.mul_left 3) using 1
  · funext k; ring
  · norm_num

/-- Quadratic simulation overhead preserves a finite expected running time.
The small prefactor `δ` is retained through the entire estimate. -/
theorem quadratic_bound (f : ℕ → ℝ) (T : ℕ) (hT : 0<T) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ t,0≤f t) (hm : Antitone f) (hstart : f 0≤δ)
    (hstep : ∀ N,f (T*(N+1)^2)≤δ*(1/2:ℝ)^N) :
    Summable f ∧ (∑' t,f t)≤11*δ*T := by
  let u : ℕ → ℕ := fun N => T*(N+1)^2
  have hu : Monotone u := by
    intro a b hab
    dsimp only [u]
    exact Nat.mul_le_mul_left T (Nat.pow_le_pow_left (by omega) 2)
  have hup (N : ℕ) : 0<u N := Nat.mul_pos hT (pow_pos (by omega) _)
  have hbound (R : ℕ) : ∑ t ∈ Finset.range R,f t≤11*δ*T := by
    have hR : R≤u R := by
      have ha : R≤(R+1)^2 := by nlinarith
      have hb := Nat.mul_le_mul_right ((R+1)^2) (show 1≤T from hT)
      exact ha.trans (by simpa only [Nat.one_mul] using hb)
    have hs := Finset.le_sum_schlomilch (f := f) (u := u)
      (by intro a b _ hab; exact hm hab) hup hu R
    have hp : ∑ t ∈ Finset.range (u 0),f t≤T*δ := by
      calc
        _ ≤ ∑ _t ∈ Finset.range (u 0),δ := Finset.sum_le_sum (fun t _ => (hm (Nat.zero_le t)).trans hstart)
        _ = T*δ := by simp [u]
    have hb (k : ℕ) : (u (k+1)-u k) • f (u k)≤
        (T:ℝ)*δ*((2*(k:ℝ)+3)*(1/2:ℝ)^k) := by
      have he : u (k+1)=u k+T*(2*k+3) := by dsimp only [u]; ring
      rw [he,Nat.add_sub_cancel_left,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,
        Nat.cast_mul,Nat.cast_ofNat]
      have hh := mul_le_mul_of_nonneg_left (hstep k) (by positivity : (0:ℝ)≤T*(2*k+3))
      exact hh.trans_eq (by ring)
    have hr : ∑ k ∈ Finset.range R,(u (k+1)-u k) • f (u k)≤10*T*δ := by
      calc
        _ ≤ ∑ k ∈ Finset.range R,(T:ℝ)*δ*((2*(k:ℝ)+3)*(1/2:ℝ)^k) :=
          Finset.sum_le_sum (fun k _ => hb k)
        _ = (T:ℝ)*δ*(∑ k ∈ Finset.range R,(2*(k:ℝ)+3)*(1/2:ℝ)^k) := by rw [Finset.mul_sum]
        _ ≤ (T:ℝ)*δ*10 := mul_le_mul_of_nonneg_left
          ((weighted_geometric.summable.sum_le_tsum (Finset.range R)
            (fun k _ => by positivity)).trans_eq weighted_geometric.tsum_eq) (by positivity)
        _ = 10*T*δ := by ring
    have hi : ∑ t ∈ Finset.range R,f t≤∑ t ∈ Finset.range (u R),f t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hR) (fun t _ _ => h0 t)
    exact (hi.trans hs).trans ((add_le_add hp hr).trans_eq (by ring))
  exact ⟨summable_of_sum_range_le h0 hbound,Real.tsum_le_of_sum_range_le h0 hbound⟩

/-- A bounded cheap prefix followed by a rare quadratic-cost correction. -/
theorem expected_time (tail : ℕ → ℝ) (S T : ℕ) (hT : 0<T) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ t,0≤tail t) (h1 : ∀ t,tail t≤1) (hm : Antitone tail)
    (hgate : tail S≤δ)
    (hstep : ∀ N,tail (S+T*(N+1)^2)≤δ*(1/2:ℝ)^N) :
    Summable tail ∧ (∑' t,tail t)≤S+11*δ*T := by
  obtain ⟨hs,hb⟩ := quadratic_bound (fun t => tail (t+S)) T hT δ hδ
    (fun t => h0 _) (fun _ _ h => hm (Nat.add_le_add_right h S))
    (by simpa only [Nat.zero_add] using hgate)
    (by intro N; simpa only [Nat.add_comm] using hstep N)
  have ht : Summable tail := (summable_nat_add_iff S).mp hs
  refine ⟨ht,?_⟩
  rw [←ht.sum_add_tsum_nat_add S]
  have hp : ∑ t ∈ Finset.range S,tail t≤(S:ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range S,(1:ℝ) := Finset.sum_le_sum (fun t _ => h1 t)
      _ = (S:ℝ) := by simp
  exact add_le_add hp hb

end ContingencyTables.QuadraticPrefixRuntime

end OAI
