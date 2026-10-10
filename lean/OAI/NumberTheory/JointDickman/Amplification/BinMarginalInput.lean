import OAI.NumberTheory.JointDickman.Amplification.BinCounts
import OAI.NumberTheory.JointDickman.Arithmetic.DickmanDistribution

namespace OAI

/-!
# The published one-variable distribution input

G. Tenenbaum, *A rate estimate in Billingsley's theorem for the size
distribution of large prime factors*, Quart. J. Math. 51 (2000), 385–403:
the unnumbered main Theorem, parts (i), (iii) at H = 0, equations (1.1),
(1.3), and the multiplicity remark following (1.7), printed pp. 386–388.
Author's corrected version: https://tenenb.perso.math.cnrs.fr/PPP/Billingsley.pdf

The input below is only its finite-bin consequence. Thresholds are the
fixed positive numbers k/J; hence finitely many ranks suffice. Continuity
of the limiting distribution permits replacing the counting endpoint by
A*x and the rank thresholds by powers of x. Its first-rank marginal is
the classical Dickman law. No statement about two different integers,
residue restrictions, weights, or short intervals is included.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

abbrev BinCountState (J : ℕ) := Fin (J-1) → Fin (J+1)

noncomputable def canonicalBinVector (J : ℕ) (x : ℝ) (n : ℕ) : BinCountState J :=
  fun i => ⟨min (binCount (primeBin x J (i.val+1)) n) J,
    (min_le_right _ _).trans_lt (Nat.lt_succ_self J)⟩

noncomputable def binStateDensity (J : ℕ) (A x : ℝ) (r : BinCountState J) : ℝ :=
  (((Ioc 0 ⌊A*x⌋₊).filter (fun n => canonicalBinVector J x n = r)).card : ℝ)/(A*x)

namespace PublishedInputs

/-- Finite-bin specialization of Tenenbaum (2000), main Theorem (i),(iii),
including the stated multiplicity version. -/
def FiniteBinDistributionInput : Prop :=
  ∀ J : ℕ, 2 ≤ J → ∃ ν : BinCountState J → ℝ,
    (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
    (∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r))) ∧
    (∀ k : ℕ, 0 < k → k < J →
      (∑ r with ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0, ν r) =
        dickmanCDF ((k : ℝ)/J))

end PublishedInputs

theorem canonicalBinVector_val {J : ℕ} (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A*x →
      ∀ i : Fin (J-1), (canonicalBinVector J x n i).val =
        binCount (primeBin x J (i.val+1)) n := by
  filter_upwards [primeBin_count_eventually_le J hJ A] with x hx n hn hnx i
  exact min_eq_left (hx (i.val+1) (by omega) n hn hnx)

theorem finite_state_sum {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (S : Finset ℕ) (v : ℕ → G) (f : G → R) :
    (∑ n ∈ S, f (v n)) = ∑ r : G, ((S.filter (fun n => v n = r)).card : R)*f r := by
  classical
  calc
    _ = ∑ n ∈ S, ∑ r : G, if v n = r then f r else 0 := by simp
    _ = ∑ r : G, ∑ n ∈ S, if v n = r then f r else 0 := sum_comm
    _ = _ := by simp only [← sum_filter,sum_const,nsmul_eq_mul]

theorem canonical_binLabel_mean
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Ioc 0 ⌊A*x⌋₊, binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n)/
        (A*x : ℂ)) atTop
      (𝓝 (∑ r : BinCountState J, (ν r : ℂ)*∏ i, ζ i^(r i).val)) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    ((Complex.continuous_ofReal.tendsto _).comp (hν A hA r)).mul_const
      (∏ i : Fin (J-1), ζ i^(r i).val))
  apply ht.congr'
  filter_upwards [canonicalBinVector_val hJ A] with x hx
  symm
  have he : ∀ n ∈ Ioc 0 ⌊A*x⌋₊,
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n =
        ∏ i, ζ i^(canonicalBinVector J x n i).val := by
    intro n hn
    have hn0 : 1 ≤ n := (mem_Ioc.mp hn).1
    rw [binLabel_apply (by omega : n ≠ 0)]
    apply prod_congr rfl
    intro i _
    rw [hx n hn0 ((Nat.le_floor_iff' (by omega : n ≠ 0)).mp (mem_Ioc.mp hn).2) i]
  rw [sum_congr rfl he,finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x)
    (fun r : BinCountState J => ∏ i, ζ i^(r i).val)]
  simp only [sum_div,Function.comp_apply,binStateDensity,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_mul]
  apply sum_congr rfl
  intro r _
  ring

end JointDickman

end OAI
