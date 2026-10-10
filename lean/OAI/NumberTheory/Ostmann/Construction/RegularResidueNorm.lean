import OAI.NumberTheory.Ostmann.ZeroDensity.PageFactors
import OAI.NumberTheory.Ostmann.Characters.AffineAction

namespace OAI

/-! # Averaged regular-transform norm on the actual CRT residue classes

The sum of the nonnegative residue test is the squarefree modulus itself.
Consequently the progression errors are summed against its exact mass, with
no pointwise estimate on the small-prime transforms.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_regular_local_norm {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (g : ZMod p → ℂ) (hg : g 0 = 0) :
    (∑ u : (ZMod p)ˣ, ‖g ((a * u⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) =
      ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  have h := ((Equiv.inv (ZMod p)ˣ).trans (Equiv.mulLeft a)).sum_comp
    (fun u : (ZMod p)ˣ => ‖g (u : ZMod p)‖ ^ 2)
  change (∑ u : (ZMod p)ˣ, ‖g ((a * u⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) = _ at h
  rw [h, sum_units_eq_sum_of_zero (fun x : ZMod p => ‖g x‖ ^ 2) (by simp [hg])]

noncomputable def regularResidueTest {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (u : (ZMod (∏ i, p i))ˣ) : ℝ :=
  ∏ i, ‖g i ((a i * (crtUnitEquiv p hc u i)⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖ ^ 2

theorem regularResidueTest_nonneg {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (u : (ZMod (∏ i, p i))ˣ) :
    0 ≤ regularResidueTest p hc a g u := Finset.prod_nonneg fun _ _ => sq_nonneg _

/-- Exact normalization (the manuscript's CRT norm identity). -/
theorem sum_regularResidueTest {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i) :
    (∑ u, regularResidueTest p hc a g u) = (∏ i, p i : ℕ) := by
  unfold regularResidueTest
  have hs := (crtUnitEquiv p hc).toEquiv.sum_comp
    (fun u => ∏ i, ‖g i ((a i * (u i)⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖ ^ 2)
  change (∑ u, ∏ i, ‖g i ((a i * (crtUnitEquiv p hc u i)⁻¹ :
      (ZMod (p i))ˣ) : ZMod (p i))‖ ^ 2) =
    (∑ u : ∀ i, (ZMod (p i))ˣ, ∏ i,
      ‖g i ((a i * (u i)⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖ ^ 2) at hs
  rw [hs]
  rw [← Fintype.prod_sum (fun i (u : (ZMod (p i))ˣ) =>
    ‖g i ((a i * u⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖ ^ 2)]
  simp only [sum_regular_local_norm, hg, henergy, Nat.cast_prod]

/-- A positive residue test can be summed against per-class progression
errors at the cost of its exact total mass. -/
theorem positive_test_progression_bound {A : Type*} [Fintype A]
    (μ ν F : A → ℝ) (δ K : ℝ) (hF : ∀ a, 0 ≤ F a)
    (hdist : ∀ a, |μ a - ν a| ≤ δ) (hν : ∀ a, ν a ≤ K) :
    (∑ a, μ a * F a) ≤ (K + δ) * ∑ a, F a := by
  calc
    _ ≤ ∑ a, (K + δ) * F a := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (by have := (abs_le.mp (hdist a)).2; linarith [hν a]) (hF a)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The regular transform estimate keeps any Page correction in `ν`;
only its pointwise factor-two bound is used here. -/
theorem regular_prime_residue_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (μ ν : (ZMod (∏ i, p i))ˣ → ℝ) (δ R : ℝ)
    (hdist : ∀ u, |μ u - ν u| ≤ δ)
    (hν : ∀ u, ν u ≤ 2 * R / Fintype.card (ZMod (∏ i, p i))ˣ) :
    (∑ u, μ u * regularResidueTest p hc a g u) ≤
      (2 * R / Fintype.card (ZMod (∏ i, p i))ˣ + δ) * (∏ i, p i : ℕ) := by
  have h := positive_test_progression_bound μ ν (regularResidueTest p hc a g) δ
    (2 * R / Fintype.card (ZMod (∏ i, p i))ˣ)
    (regularResidueTest_nonneg p hc a g) hdist hν
  rwa [sum_regularResidueTest p hc a g hg henergy] at h

private theorem totient_factor_le_exp (x : ℝ) (hx : 2 ≤ x) :
    x / (x - 1) ≤ Real.exp (2 / x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hinv : 1 / (x - 1) ≤ 2 / x :=
    (div_le_div_iff₀ hx1 hx0).mpr (by linarith)
  calc
    _ = 1 + 1 / (x - 1) := by field_simp; ring
    _ ≤ 1 + 2 / x := add_le_add_right hinv 1
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (2 / x)

/-- The CRT unit-density correction is close to one when all slot primes
are large compared with their number. -/
theorem regular_unit_ratio_le_exp {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (Z : ℝ) (hZ : 2 ≤ Z) (hpZ : ∀ i, Z ≤ p i) :
    ((∏ i, p i : ℕ) : ℝ) / Fintype.card (ZMod (∏ i, p i))ˣ ≤
      Real.exp (2 * Fintype.card I / Z) := by
  have hZ0 : 0 < Z := by linarith
  have hfactor (i : I) :
      (p i : ℝ) / Fintype.card (ZMod (p i))ˣ ≤ Real.exp (2 / Z) := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : (p i).Prime).one_lt.le, Nat.cast_one]
    apply (totient_factor_le_exp (p i) (hZ.trans (hpZ i))).trans
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (by norm_num) hZ0 (hpZ i)
  have hcard := Fintype.card_congr (crtUnitEquiv p hc).toEquiv
  rw [hcard, Fintype.card_pi, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  calc
    _ ≤ ∏ _i : I, Real.exp (2 / Z) := Finset.prod_le_prod₀
      (fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (fun i _ => hfactor i)
    _ = Real.exp (2 * Fintype.card I / Z) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring

end Ostmann

end OAI
