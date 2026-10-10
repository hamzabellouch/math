import OAI.NumberTheory.Jacobsthal.Estimates.SourceSquareScale
import OAI.NumberTheory.Jacobsthal.Estimates.SourceValueSmallness
import OAI.NumberTheory.Jacobsthal.Sieve.IntegerSlopeConstruction

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

theorem source_coefficient_log_bound {z R cost : ℝ} {H : ℕ}
    (hR : 0 < R) (hL : 0 < Real.log z) (hcost0 : 0 ≤ cost)
    (hcost : cost ≤ 4*R^2/(Real.log z)^6)
    (hheight : Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((sourceDegree z R : ℝ)+2)*cost) :
    Real.log (2*(H : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4 := by
  apply hheight.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (2*(Real.log z)^2/R)*cost := mul_le_mul_of_nonneg_right (source_degree_factor hR hL) hcost0
    _ ≤ (2*(Real.log z)^2/R)*(4*R^2/(Real.log z)^6) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = 8*R/(Real.log z)^4 := by field_simp; ring

theorem source_value_log_budget {z R S : ℝ} {H : ℕ}
    (hz : 2 ≤ z) (hR : 0 < R) (hRz : R ≤ z) (hL : 1 ≤ Real.log z)
    (hH : 0 < H) (hS : S ≤ z^3)
    (hheight : Real.log (2*(H : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4) :
    logarithmicValueBudget (sourceDegree z R) H S ≤
      4*Real.log z+Real.log 4+8*R/(Real.log z)^4+3*R/Real.log z := by
  have hL0 : 0 < Real.log z := by linarith
  have hN := source_dimension_log_bound hz hR.le hRz hL
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : Real.log (H : ℝ) ≤ Real.log 4+8*R/(Real.log z)^4 :=
    (Real.log_le_log hH0 (by linarith : (H : ℝ) ≤ 2*(H : ℝ))).trans hheight
  have hM0 : (0 : ℝ) < max 1 S := zero_lt_one.trans_le (le_max_left _ _)
  have hM : max 1 S ≤ z^3 := max_le (one_le_pow₀ (by linarith : 1 ≤ z)) hS
  have hlogM : Real.log (max 1 S) ≤ 3*Real.log z := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hM0 hM
  have hlogM0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hprod : (sourceDegree z R : ℝ)*Real.log (max 1 S) ≤ 3*R/Real.log z := by
    calc
      _ ≤ (R/(Real.log z)^2)*(3*Real.log z) :=
        mul_le_mul (sourceDegree_le hR.le) hlogM hlogM0 (by positivity)
      _ = _ := by field_simp
  unfold logarithmicValueBudget
  linarith

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial ErdosInversePrimeBin

structure SourcePolynomialWitness (z R xi S eta c : ℝ)
    (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ) where
  polynomial : MvPolynomial (Fin 2) ℤ
  height : ℕ
  nonzero : polynomial ≠ 0
  degree_le : polynomial.totalDegree ≤ sourceDegree z R
  height_pos : 0 < height
  coefficient_bound : ∀ m : Fin 2 →₀ ℕ, |polynomial.coeff m| ≤ (height : ℤ)
  line_vanishing : ∀ p : primeBin R xi, ∀ s ∈ T p,
    lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) polynomial = 0
  height_bound : Real.log (2*(height : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4
  value_budget : logarithmicValueBudget (sourceDegree z R) height S < c*eta*R/4
  rich_vanishing : ∀ (x y : ℤ), (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) →
    (0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) → ∀ (I : Finset ℕ) (hIP : I ⊆ primeBin R xi),
    c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) →
    (∀ p : I, IntegerLineIncidence (primeBin R xi) T a x y ⟨p.val,hIP p.property⟩) →
    MvPolynomial.eval ![x,y] polynomial = 0

theorem uniform_polynomial_for_bounded_square (eta alpha c : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → S ≤ z^3 →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        Nonempty (SourcePolynomialWitness z R xi S eta c T a) := by
  obtain ⟨R0,hR0⟩ := Filter.eventually_atTop.mp (uniform_prime_bin_budgets heta)
  have hbig := (tendsto_rpow_atTop halpha).eventually_ge_atTop R0
  filter_upwards [eventual_value_budget_small alpha (c*eta/4) halpha (by positivity),hbig]
    with z hsmall hbig
  refine ⟨hsmall.1,hsmall.2.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 hS T a hthin
  have hbin := hR0 R (hbig.trans hRlo)
  have hR : 0 < R := by linarith [hbin.1]
  have hL : 0 < Real.log z := by linarith [hsmall.2.1]
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hRz : R ≤ z := by
    apply hRhi.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith [hsmall.1] : 1 ≤ z) (by norm_num : (1 : ℝ)/100 ≤ 1)
  have hprime : ∀ p ∈ primeBin R xi, Nat.Prime p := fun p hp =>
    ((mem_primeBin hR.le hxi0 p).mp hp).1
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hheight,hlift⟩ :=
    exists_integer_auxiliary_polynomial_lifting (primeBin R xi) hprime T a (sourceDegree z R)
  have hbudgets := hbin.2 xi hxi hxi1
  have hcost := hbudgets.1 (Real.log z) hL T hthin
  have hcost0 : 0 ≤ ∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_of_lt (hprime p p.property).pos
  have hheight' := source_coefficient_log_bound hR hL hcost0 hcost hheight
  have hvalue := source_value_log_budget hsmall.1 hR hRz hsmall.2.1 hH hS hheight'
  have hstrict : logarithmicValueBudget (sourceDegree z R) H S < c*eta*R/4 := by
    have h := hvalue.trans_lt (hsmall.2.2 R hRlo)
    convert! h using 1
    ring
  refine ⟨{
    polynomial := Q
    height := H
    nonzero := hQ
    degree_le := hD
    height_pos := hH
    coefficient_bound := hcoeff
    line_vanishing := hline
    height_bound := hheight'
    value_budget := hstrict
    rich_vanishing := ?_ }⟩
  intro x y hx hy I hIP hrich hinc
  exact hlift S x y hx hy I hIP hinc (hstrict.trans_le (hbudgets.2 c hc.le I hIP hrich))

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial ErdosInversePrimeBin ErdosInverseBoxHeight

theorem uniform_original_source_polynomial (C eta alpha c : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        Nonempty (SourcePolynomialWitness z R xi S eta c T a) := by
  filter_upwards [uniform_polynomial_for_bounded_square eta alpha c heta halpha hc,
    uniform_source_square_scale C hC] with z hpoly hscale
  refine ⟨hpoly.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 T a hthin
  have hR1 : 1 ≤ R := (Real.one_le_rpow (by linarith [hpoly.1] : 1 ≤ z) halpha.le).trans hRlo
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hS := hscale.2.2 S R p q xi hp hq hpq hratio hinfl hR1 hRhi hxi0 hxi1
  exact hpoly.2.2 R xi S hRlo hRhi hxi hxi1 hS T a hthin

end ErdosSourcePolynomial

end

end Erdos970

end OAI
