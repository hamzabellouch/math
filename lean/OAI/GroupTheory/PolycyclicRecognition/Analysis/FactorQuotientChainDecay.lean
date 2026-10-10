import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientChainDecay
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts

namespace OAI

/-! # Negative-height factor lifts imply quotient endpoint contraction -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

variable {N D G E Q J : Type*} [Group N] [Group D] [Group G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]

/-- The nilpotent parts of the point lifts cancel. Polynomial bounds on
the Cartan parts and negative height turn the compact increment estimate
into a vanishing ordered quotient product. -/
theorem factor_quotient_chain_difference_tendsto_one
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q)
      (GroupLieAlgebra (𝓘(ℝ, E)) Q) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (K : Set Q)
    {A rate : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (p : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖b.equivFun (chart.symm (α d q))‖ ≤
        A * (1 + size d) ^ p * Real.exp (rate * height d))
    (m : ℕ → ℕ) (y : ℕ → ℕ → G) (u : ℕ → ℕ → N) (d : ℕ → ℕ → D)
    {B gap count : ℝ} (hB : 0 ≤ B) (hgap : 0 < gap) (degree countDegree : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
    (hlifts : ∀ᶠ n in atTop, ∀ i < m n,
      ι (u n i) * κ (d n i) = y n i ∧
      0 ≤ size (d n i) ∧ size (d n i) ≤ B * (1 + (n : ℝ)) ^ degree ∧
      height (d n i) ≤ -gap * n)
    (hsteps : ∀ᶠ n in atTop, ∀ i < m n,
      act ((y n i)⁻¹ * y n (i + 1)) 1 ∈ K) :
    Tendsto (fun n => (act (y n 0) 1)⁻¹ * act (y n (m n)) 1)
      atTop (𝓝 (1 : Q)) := by
  obtain ⟨C, hC, hbr⟩ := exists_basis_structureConstant_bound b
  apply quotient_chain_difference_tendsto_one dynkin Exp hExp chart hchart hc b hC hbr m
    (fun n i => act (y n i) 1) (A := A * (1 + B) ^ p)
    (by positivity) (mul_pos hrate hgap) (degree * p) countDegree hcount
  filter_upwards [hlifts, hsteps] with n hn hstep
  intro i hi
  obtain ⟨hlift, hsize0, hsize, hheight⟩ := hn i hi
  rw [factor_quotient_increment ι κ π α act hact _ _ (u n i) (d n i) hlift]
  have hneg : height (d n i) ≤ 0 := hheight.trans (by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hgap.le) (Nat.cast_nonneg n))
  have hb : 1 + size (d n i) ≤ (1 + B) * (1 + (n : ℝ)) ^ degree := by
    have hp : 1 ≤ (1 + (n : ℝ)) ^ degree := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith
  have hpoly : (1 + size (d n i)) ^ p ≤
      (1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p) := by
    calc
      _ ≤ ((1 + B) * (1 + (n : ℝ)) ^ degree) ^ p :=
        pow_le_pow_left₀ (by linarith) hb _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hexp : Real.exp (rate * height (d n i)) ≤ Real.exp (-(rate * gap) * n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hheight hrate.le
    nlinarith
  calc
    _ ≤ A * (1 + size (d n i)) ^ p * Real.exp (rate * height (d n i)) :=
      hcontract (d n i) hneg _ (hstep i hi)
    _ ≤ A * ((1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p)) *
        Real.exp (-(rate * gap) * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly hA) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
