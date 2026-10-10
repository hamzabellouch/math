import OAI.NumberTheory.TotientAsymptotic.TailProductBounds
import OAI.NumberTheory.TotientAsymptotic.CollisionCoordinateEndpoint

namespace OAI

/-!
Local value and right-preimage prime bounds from the actual candidate
prime product.  A late residual is controlled by its own coordinate
envelope, rather than by the original ambient counting parameter.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptLocalValueHeight (d H : ℕ) (T : ℝ) : ℝ :=
  T+Real.log (Real.log (d : ℝ)+(H : ℝ)+1)

lemma ppt_local_value_height_nonneg {d H : ℕ} {T : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) : 0 ≤ pptLocalValueHeight d H T := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hbase : 1 ≤ Real.log (d : ℝ)+(H : ℝ)+1 := by
    linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]
  exact add_nonneg hT (Real.log_nonneg hbase)

/-- The seed-times-totient value is bounded directly by the sum of the
logarithms of the actual primes. -/
lemma ppt_seed_totient_prime_product_log_le {d n : ℕ} {T : ℝ}
    (hd : 0 < d) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T) :
    Real.log ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.log (d : ℝ)+(n : ℝ)*Real.exp T := by
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hφ : 0 < (∏ i, p i).totient := Nat.totient_pos.mpr hprod
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφR : (0 : ℝ) < (∏ i, p i).totient := by exact_mod_cast hφ
  have hφlog := Real.log_le_log hφR
    (Nat.cast_le.mpr (Nat.totient_le (∏ i, p i)))
  have hprodlog := prime_tail_log_bound p hp (by
    intro i
    simpa only [primePrefixCoord, B] using hcoords i)
  rw [Nat.cast_mul, Real.log_mul hdR.ne' hφR.ne']
  linarith only [hφlog, hprodlog]

/-- A product with at most `H+1` prime factors has value below the
double-exponential endpoint of its local coordinate height. -/
theorem ppt_local_prime_product_value_bound {d n H : ℕ} {T : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hn : n ≤ H+1)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T) :
    ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.exp (Real.exp (pptLocalValueHeight d H T)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hbase : 1 ≤ Real.log (d : ℝ)+(H : ℝ)+1 := by
    linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]
  have hnR : (n : ℝ) ≤ (H : ℝ)+1 := by exact_mod_cast hn
  have hseed := mul_le_mul_of_nonneg_left (Real.one_le_exp hT) hlogd
  have hdim := mul_le_mul_of_nonneg_right hnR (Real.exp_pos T).le
  have hlog : Real.log ((d*(∏ i, p i).totient : ℕ) : ℝ) ≤
      Real.exp (pptLocalValueHeight d H T) := by
    apply (ppt_seed_totient_prime_product_log_le hd p hp hcoords).trans
    unfold pptLocalValueHeight
    rw [Real.exp_add, Real.exp_log (zero_lt_one.trans_le hbase)]
    nlinarith only [hseed, hdim]
  have hv : (0 : ℝ) < (d*(∏ i, p i).totient : ℕ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hp i).pos)))
  simpa only [Real.exp_log hv] using Real.exp_le_exp.mpr hlog

/-- Every prime in any preimage of the local value has its predecessor
below the same endpoint.  This retains all right preimages. -/
theorem ppt_local_preimage_prime_predecessor_bound {d n H u q : ℕ} {T : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hn : n ≤ H+1)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T)
    (_hu : 0 < u) (hvalue : u.totient = d*(∏ i, p i).totient)
    (hq : q.Prime) (hqu : q ∣ u) :
    ((q-1 : ℕ) : ℝ) ≤ Real.exp (Real.exp (pptLocalValueHeight d H T)) := by
  have hdiv : q-1 ∣ d*(∏ i, p i).totient := by
    simpa only [Nat.totient_prime hq, hvalue] using Nat.totient_dvd_of_dvd hqu
  have hv : 0 < d*(∏ i, p i).totient :=
    Nat.mul_pos hd (Nat.totient_pos.mpr (Finset.prod_pos (fun i _ => (hp i).pos)))
  exact (Nat.cast_le.mpr (Nat.le_of_dvd hv hdiv)).trans
    (ppt_local_prime_product_value_bound hd hT hn p hp hcoords)

/-- The local sieve for an arbitrary right head can use this endpoint
height, up to the harmless predecessor-to-prime error of one. -/
theorem ppt_local_preimage_prime_coordinate_bound {d n H u q : ℕ} {T : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hn : n ≤ H+1)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hcoords : ∀ i, B (p i) ≤ T)
    (hu : 0 < u) (hvalue : u.totient = d*(∏ i, p i).totient)
    (hq : q.Prime) (hq3 : 3 ≤ q) (hqu : q ∣ u) :
    B q ≤ pptLocalValueHeight d H T+1 := by
  have hheight := ppt_local_value_height_nonneg (H := H) hd hT
  have hendpoint : Real.exp 1 ≤ Real.exp (Real.exp (pptLocalValueHeight d H T)) :=
    Real.exp_le_exp.mpr (Real.one_le_exp hheight)
  have hbound := prime_coordinate_endpoint_bound hq3 hendpoint
    (ppt_local_preimage_prime_predecessor_bound hd hT hn p hp hcoords hu hvalue hq hqu)
  simpa only [B_exp_exp] using hbound

end TotientAsymptotic

end

end OAI
