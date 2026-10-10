import OAI.Probability.DilutedSpin.SizeSpinRoot

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma stemMeanAt_bound (S : PrescribedTree n) (r : ℕ) (d : Fin (r+1))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (hf : ∀ x, |f x|≤1) (x : FinitePath Ω (n+r)) :
    |stemMeanAt S r d T f x|≤1 := by
  induction r with
  | zero => exact treeMean_bound S T hf
  | succ r ih =>
    refine Fin.cases ?_ (fun e => ?_) d
    · exact treeMean_bound (stem S (r+1)) T hf
    · exact ih e (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

/-- The actual change of a product of proper-child conditional means, when
its common evaluation depth advances by one on the SAME full sampled path. -/
noncomputable def productStemIncrementSq {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) : ℝ :=
  (KernelTower.law (n+r) T).expect (fun x =>
    ((∏ i, stemMeanAt (C i) r d.succ T f x)-
      (∏ i, stemMeanAt (C i) r d.castSucc T f x))^2)

lemma productStemIncrementSq_nonneg {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) :
    0≤productStemIncrementSq C r T f d :=
  FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

lemma productStemIncrementSq_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) (d : Fin r) :
    productStemIncrementSq C r T f d ≤
      (Fintype.card ι:ℝ)*∑ i, stemIncrementSq (C i) r T f d := by
  have h := (KernelTower.law (n+r) T).expect_mono (fun x =>
    bounded_product_difference_sq
      (fun i => stemMeanAt (C i) r d.succ T f x)
      (fun i => stemMeanAt (C i) r d.castSucc T f x)
      (fun i => stemMeanAt_bound (C i) r _ T f hf x)
      (fun i => stemMeanAt_bound (C i) r _ T f hf x))
  simpa only [productStemIncrementSq,stemIncrementSq,FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] using h

/-- Finite product martingale-energy bound. Only the number of proper
children occurs in the constant, not the depth, dimension or kernels. -/
theorem sum_productStemIncrementSq_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) :
    (∑ d : Fin r, productStemIncrementSq C r T f d) ≤ (Fintype.card ι:ℝ)^2 := by
  calc
    _ ≤ ∑ d : Fin r, (Fintype.card ι:ℝ)*∑ i, stemIncrementSq (C i) r T f d :=
      Finset.sum_le_sum (fun d _ => productStemIncrementSq_le C r T f hf d)
    _ = (Fintype.card ι:ℝ)*∑ i, ∑ d : Fin r, stemIncrementSq (C i) r T f d := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (Fintype.card ι:ℝ)*∑ i : ι, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        sum_stemIncrementSq_le_one (C i) r T f hf)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two]

/-- The evaluation-depth component of the manuscript's h_N error, with its
literal 1/L normalization and spatial average. Zero spatial size is included. -/
theorem averaged_productStemIncrement_spatial_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r L : ℕ) (U : Finset (Fin r))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ)
    (hf : ∀ x j, |f x j|≤1) :
    ((∑ d ∈ U, (∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ))/(L:ℝ)) ≤
      (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero,Finset.sum_const_zero]
    positivity
  · rw [← Finset.sum_div,Finset.sum_comm]
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    calc
      _ ≤ ∑ j : Fin N, (Fintype.card ι:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.sum_le_univ_sum_of_nonneg (productStemIncrementSq_nonneg C r T (fun x => f x j))).trans
          (sum_productStemIncrementSq_le C r T (fun x => f x j) (fun x => hf x j))
      _ = _ := by simp [mul_comm]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
