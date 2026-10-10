import OAI.NumberTheory.JointDickman.Probability.SignedSplitProduct
import OAI.NumberTheory.JointDickman.Probability.ChannelNorm

namespace OAI

/-! # Exact identification of signed split masses and the actual channel -/

namespace JointDickman
open Finset

noncomputable def primeSplitProductSupport (P : Finset ℕ) : Finset ℕ :=
  P.powerset.image (fun A => ∏ p ∈ A, p)

noncomputable def subsetSiteTest (P : Finset ℕ) (g : (P → Bool) → ℝ)
    (S : Finset ℕ) : ℝ := g (fun p => decide (p.val ∈ S))

theorem retainedPrimeProduct_subset (P : Finset ℕ) (S : P.powerset) :
    retainedPrimeProduct P (subsetHitEquiv P S) = ∏ p ∈ S.val, p := by
  rw [retainedPrimeProduct_selected]
  congr 1
  ext p
  by_cases hp : p ∈ P
  · simp [selectedPrimeSubset, subsetHitEquiv, hp]
  · have hs : p ∉ S.val := fun hs => hp (mem_powerset.mp S.property hs)
    simp [selectedPrimeSubset, hp, hs]

theorem fullPrimeMass_subset (P : Finset ℕ) (S : P.powerset) :
    fullPrimeMass P (subsetHitEquiv P S) =
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S.val :=
by
  simpa only [fullPrimeMass, bernoulliSiteMass] using
    bernoulliSubsetMass_eq_product P (fun p : ℕ => 1/(p : ℝ)) S

/-- Push the finite signed split measure forward to its integer product. -/
theorem signedSplitProductMass_sum (P : Finset ℕ) (g : Finset ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, signedSplitProductMass P g n * F n) =
      ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S *
        ∑ A ∈ P.powerset, subsetRetentionMass S A * F (∏ p ∈ A, p) := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  rw [sum_eq_single (∏ p ∈ A, p)]
  · simp
    ring
  · intro n _ hn
    simp [Ne.symm hn]
  · intro hn
    exact False.elim (hn (mem_image.mpr ⟨A, hA, rfl⟩))

/-- The signed integer-product law is exactly the original fair-split expectation. -/
theorem signedSplitProductMass_expectation (P : Finset ℕ)
    (g : (P → Bool) → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P,
      signedSplitProductMass P (subsetSiteTest P g) n * F n) =
      ∑ x : P → Bool, fullPrimeMass P x * g x *
        ∑ y : P → Bool, fairRetentionMass x y * F (retainedPrimeProduct P y) := by
  classical
  rw [signedSplitProductMass_sum]
  rw [← (subsetHitEquiv P).sum_comp]
  simp_rw [← (subsetHitEquiv P).sum_comp
    (fun y => fairRetentionMass _ y * F (retainedPrimeProduct P y))]
  simp_rw [fullPrimeMass_subset, fairRetentionMass_subsets, retainedPrimeProduct_subset]
  rw [← sum_coe_sort P.powerset]
  apply sum_congr rfl
  intro S _
  rw [sum_coe_sort P.powerset
    (fun A => subsetRetentionMass S.val A * F (∏ p ∈ A, p))]
  rfl

/-- A channel cell contains exactly the corresponding signed integer masses. -/
theorem signedSplitProductMass_channel {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finset ℕ) (g : (P → Bool) → ℝ) (cell : ℕ → Option A)
    (μ : A → ℝ) (a : A) (hμ : μ a ≠ 0) :
    (∑ n ∈ primeSplitProductSupport P, if cell n = some a then
      signedSplitProductMass P (subsetSiteTest P g) n else 0) =
      μ a * finiteChannel (fullPrimeMass P) μ (partialFairPrimeTransition P cell) g a := by
  classical
  have h := signedSplitProductMass_expectation P g
    (fun n => if cell n = some a then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h, finiteChannel, mul_div_cancel₀ _ hμ]
  apply sum_congr rfl
  intro x _
  unfold partialFairPrimeTransition optionCellMass
  ring

/-- The manuscript normalization is delta/phi, with no approximation. -/
theorem manuscriptChannel_cell_mass {m₁ B q : ℕ} [NeZero q]
    (hm : 0 < m₁) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ) :
    (∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      if logResidueCell B q (channelLower (channelFineCount m₁ B))
        (channelUpper (channelFineCount m₁ B)) n = some a then
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n
      else 0) =
      (channelMesh (channelFineCount m₁ B)/(q.totient : ℝ))*
        manuscriptChannel m₁ B q g a := by
  apply signedSplitProductMass_channel
  exact (div_pos (channelMesh_pos (channelFineCount_pos hm hB))
    (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))).ne'

end JointDickman

end OAI
