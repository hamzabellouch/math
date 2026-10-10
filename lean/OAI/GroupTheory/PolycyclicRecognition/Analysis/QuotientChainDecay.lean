import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinProductTails
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorQuotientAction

namespace OAI

/-! # Contracting quotient increments along the actual factor lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- The quotient increment is the actual Cartan action on the relative
ambient increment. Dependence on the nilpotent factor cancels exactly. -/
theorem factor_quotient_increment
    {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (x y : G) (u : N) (d : D) (hx : ι u * κ d = x) :
    (act x 1)⁻¹ * act y 1 = α d (act (x⁻¹ * y) 1) := by
  have he : act y 1 = act x (act (x⁻¹ * y) 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [he, ← hx, hact, hact, map_one, mul_one, inv_mul_cancel_left]

/-- Ordered products of successive differences telescope without
commutativity. -/
theorem prod_chain_differences {Q : Type*} [Group Q] (f : ℕ → Q) (n : ℕ) :
    (List.ofFn (fun i : Fin n => (f i)⁻¹ * f (i + 1))).prod = (f 0)⁻¹ * f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ']
    simp only [Fin.val_castSucc, Fin.val_last, List.prod_concat]
    rw [ih]
    simp [mul_assoc]

variable {E Q J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]

/-- Polynomially many quotient increments at negative linear height
have asymptotically equal endpoints. All increments are the chart
logarithms of the actual successive quotients. -/
theorem quotient_chain_difference_tendsto_one
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q)
      (GroupLieAlgebra (𝓘(ℝ, E)) Q) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (m : ℕ → ℕ) (f : ℕ → ℕ → Q)
    {A K rate : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (p q : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ K * (1 + (n : ℝ)) ^ q)
    (hstep : ∀ᶠ n in atTop, ∀ i < m n,
      ‖b.equivFun (chart.symm ((f n i)⁻¹ * f n (i + 1)))‖ ≤
        A * (1 + (n : ℝ)) ^ p * Real.exp (-rate * n)) :
    Tendsto (fun n => (f n 0)⁻¹ * f n (m n)) atTop (𝓝 (1 : Q)) := by
  let X := fun n (i : Fin (m n)) => chart.symm ((f n i)⁻¹ * f n (i + 1))
  have hsmall : Tendsto (fun n => ∑ i, ‖b.equivFun (X n i)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun i _ => norm_nonneg _)))
      (show ∀ᶠ n in atTop, (∑ i, ‖b.equivFun (X n i)‖) ≤
        (K * A) * (1 + (n : ℝ)) ^ (p + q) * Real.exp (-rate * n) from ?_)
      ((summable_polynomial_exp_decay (K * A) (p + q) hrate).tendsto_atTop_zero)
    filter_upwards [hcount, hstep] with n hn hs
    calc
      _ ≤ ∑ _i : Fin (m n), A * (1 + (n : ℝ)) ^ p * Real.exp (-rate * n) :=
        Finset.sum_le_sum (fun i _ => hs i i.isLt)
      _ = (m n : ℝ) * (A * (1 + (n : ℝ)) ^ p * Real.exp (-rate * n)) := by simp
      _ ≤ (K * (1 + (n : ℝ)) ^ q) *
          (A * (1 + (n : ℝ)) ^ p * Real.exp (-rate * n)) :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hcontinuous : Continuous Exp := by
    convert chart.continuous using 1
    exact (funext hchart).symm
  have ht := finite_exp_products_tendsto_one dynkin Exp hExp hcontinuous hc b hC hbracket m X hsmall
  have he (n : ℕ) : (List.ofFn (fun i => Exp (X n i))).prod = (f n 0)⁻¹ * f n (m n) := by
    have hexp (i : Fin (m n)) : Exp (X n i) = (f n i)⁻¹ * f n (i + 1) := by
      rw [← hchart, chart.apply_symm_apply]
    simp_rw [hexp]
    exact prod_chain_differences (f n) (m n)
  simpa only [he] using ht

end PolycyclicRecognition

end

end OAI
