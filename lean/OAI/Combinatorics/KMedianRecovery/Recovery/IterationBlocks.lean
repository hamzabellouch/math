import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.State

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma growth_up_to (f : ℕ → ℝ) (g : ℝ) (hg : 0≤g) (T : ℕ)
    (hf : ∀ t<T, g*f t≤f (t+1)) : g^T*f 0≤f T := by
  have h (k : ℕ) (hk : k≤T) : g^k*f 0≤f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = g*(g^k*f 0) := by rw [pow_succ]; ring
        _ ≤ g*f k := mul_le_mul_of_nonneg_left (ih (by omega)) hg
        _ ≤ _ := hf k (by omega)
  exact h T le_rfl

lemma iterate_invalid_before {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (T t : ℕ) (ht : t≤T)
    (hT : ¬∀ r∈rows, r.Holds (iterate D rows S T).center) :
    ¬∀ r∈rows, r.Holds (iterate D rows S t).center := by
  intro hh
  have he := iterate_stable D rows S t (T-t) hh
  rw [Nat.add_sub_of_le ht] at he
  exact hT (he.symm ▸ hh)

lemma iterate_determinant_growth {n : ℕ} (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (T : ℕ) (hT : ¬∀ r∈rows, r.Holds (iterate (gridDenominator n T) rows S T).center)
    (x : Fin n → ℝ) (hx : ∀ r∈rows, r.RealHolds x) :
    (1+1/(2*(n:ℝ)))^T*(realMatrix S.shape)⁻¹.det≤
      (realMatrix (iterate (gridDenominator n T) rows S T).shape)⁻¹.det := by
  let D := gridDenominator n T
  have hD := gridDenominator_pos n T (by omega)
  have hg : 0≤1+1/(2*(n:ℝ)) := by positivity
  apply growth_up_to (fun t => (realMatrix (iterate D rows S t).shape)⁻¹.det) _ hg T
  intro t ht
  let St := iterate D rows S t
  have hbad : ¬∀ r∈rows, r.Holds St.center := iterate_invalid_before D rows S T t ht.le hT
  have hrow : ∃ r, badRow rows St.center=some r := by
    cases he : badRow rows St.center with
    | none => exact (hbad ((badRow_none rows St.center).mp he)).elim
    | some r => exact ⟨r,rfl⟩
  obtain ⟨r,hr⟩ := hrow
  have ha := badRow_nonzero rows St.center r hr x hx
  have hp := iterate_pos D hD rows S hn hS t
  have hlo := iterate_shape_lower D hD rows S hn hS h0 t
  have hpre := inflatedShape_precision St.shape r.coeff (by simpa using hn) hp ha t T ht.le hlo
  have hpr : 2*(Fintype.card (Fin n):ℝ)/(D:ℝ)≤
      (1/(8*(Fintype.card (Fin n):ℝ)^2))*(1/3:ℝ)^(T+1) := by
    simpa only [Fintype.card_fin,D] using (gridDenominator_precision n T (by omega)).le
  have hh := rational_step_growth D hD St.shape r.coeff (by simpa using hn) hp ha
    ((1/3:ℝ)^(T+1)) hpre hpr
  change (1+1/(2*(n:ℝ)))*(realMatrix St.shape)⁻¹.det≤
    (realMatrix (advance D rows St).shape)⁻¹.det
  simpa only [advance,hr,ite_eq_right ha,Fintype.card_fin] using hh

lemma iterate_block_growth {n : ℕ} (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (L : ℕ) (hT : ¬∀ r∈rows, r.Holds (iterate (gridDenominator n (2*n*L)) rows S (2*n*L)).center)
    (x : Fin n → ℝ) (hx : ∀ r∈rows, r.RealHolds x) :
    (2:ℝ)^L*(realMatrix S.shape)⁻¹.det≤
      (realMatrix (iterate (gridDenominator n (2*n*L)) rows S (2*n*L)).shape)⁻¹.det := by
  have hh := iterate_determinant_growth rows S hn hS h0 (2*n*L) hT x hx
  have hb := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (robust_block_growth n (by omega)) L
  rw [←pow_mul] at hb
  exact (mul_le_mul_of_nonneg_right hb hS.inv.det_pos.le).trans hh

lemma factorial_bit_bound (n : ℕ) : (n.factorial:ℝ)≤(2:ℝ)^(n*n) := by
  have h : n.factorial≤2^(n*n) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^n)^n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = _ := by rw [pow_mul]
  exact_mod_cast h

def iterationBlocks (n p s : ℕ) : ℕ := n*n+2*n*(p+s)+1

def iterationBudget (n p s : ℕ) : ℕ := 2*n*iterationBlocks n p s

lemma determinant_budget (n p s : ℕ) (R r : ℝ) (hR : 0<R) (hr : 0<r)
    (hRp : R≤(2:ℝ)^s) (hrp : 1/r≤(2:ℝ)^p) :
    (n.factorial:ℝ)*(1/r^2)^n < (2:ℝ)^(iterationBlocks n p s)*(1/R^2)^n := by
  have hratio : R/r≤(2:ℝ)^(p+s) := by
    calc
      _ = (1/r)*R := by ring
      _ ≤ (2:ℝ)^p*2^s := mul_le_mul hrp hRp hR.le (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hp := pow_le_pow_left₀ (div_nonneg hR.le hr.le) hratio (2*n)
  have hall := mul_le_mul (factorial_bit_bound n) hp (by positivity) (by positivity)
  have he : (2:ℝ)^(n*n)*((2:ℝ)^(p+s))^(2*n)=(2:ℝ)^(n*n+2*n*(p+s)) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [he] at hall
  have hlt : (2:ℝ)^(n*n+2*n*(p+s))<(2:ℝ)^(iterationBlocks n p s) := by
    apply pow_lt_pow_right₀ (by norm_num)
    exact Nat.lt_succ_self _
  have hbound := hall.trans_lt hlt
  have heq : (n.factorial:ℝ)*(1/r^2)^n=
      ((n.factorial:ℝ)*(R/r)^(2*n))*(1/R^2)^n := by
    simp only [pow_mul,div_pow,one_pow]
    field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_right hbound (by positivity)

end MetricKMedianRecovery.Ellipsoid

end OAI
