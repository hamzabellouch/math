import OAI.Probability.DilutedSpin.CoordinateFiber
import OAI.Probability.DilutedSpin.ProductEvaluationContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- Squared norm of the change of the two-leaf contraction in its actual
joint target law, not a product of its marginals. -/
noncomputable def targetContractionChangeSq (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (X Y : FinitePath Ω n → Fin N → ℝ) : ℝ :=
  (S.sampleLaw T).expect (fun z =>
    (FiniteLaw.dot (X (S.pathAt a z)) (X (S.pathAt b z))-
      FiniteLaw.dot (Y (S.pathAt a z)) (Y (S.pathAt b z)))^2)

lemma targetContractionChangeSq_nonneg (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (X Y : FinitePath Ω n → Fin N → ℝ) :
    0 ≤ targetContractionChangeSq S T a b X Y :=
  FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

/-- Exact leaf marginalization gives a uniform comparison for any target,
even one depending on the evaluation depth and all its branching coordinates. -/
lemma targetContractionChangeSq_le (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (X Y : FinitePath Ω n → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) :
    targetContractionChangeSq S T a b X Y ≤
      4*(KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i)) := by
  have h := (S.sampleLaw T).expect_mono (fun z => FiniteLaw.dot_pair_change_sq
    (X (S.pathAt a z)) (X (S.pathAt b z)) (Y (S.pathAt a z)) (Y (S.pathAt b z))
    (hX _) (hX _) (hY _) (hY _))
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_left,
    leaf_marginal S T a (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i)),
    leaf_marginal S T b (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))] at h
  exact h.trans_eq (by ring)

/-- Actual product of the proper-child conditional means on a single path. -/
noncomputable def productStemMeanAt {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (d : Fin (r+1)) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → Fin N → ℝ) (x : FinitePath Ω (n+r)) (j : Fin N) : ℝ :=
  ∏ i, stemMeanAt (C i) r d T (fun y => f y j) x

lemma productStemMeanAt_bound {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (d : Fin (r+1)) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → Fin N → ℝ) (hf : ∀ x j, |f x j|≤1)
    (x : FinitePath Ω (n+r)) (j : Fin N) : |productStemMeanAt C r d T f x j|≤1 := by
  unfold productStemMeanAt
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ =>
    stemMeanAt_bound (C i) r d T (fun y => f y j) (fun y => hf y j) x)

lemma productStemMeanAt_spatial_increment {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r : ℕ) (d : Fin r) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → Fin N → ℝ) :
    (KernelTower.law (n+r) T).expect (fun x => FiniteLaw.spatialSq (fun i =>
      productStemMeanAt C r d.succ T f x i-productStemMeanAt C r d.castSucc T f x i))=
      (∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ) := by
  simp only [FiniteLaw.spatialSq,FiniteLaw.expect_div,FiniteLaw.expect_fintype_sum,
    productStemMeanAt,productStemIncrementSq]

 
theorem averaged_target_evaluation_change_le {ι : Type*} [Fintype ι]
    (C : ι → PrescribedTree n) (r L : ℕ) (U : Finset (Fin r))
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ)
    (hf : ∀ x j, |f x j|≤1)
    (Target : Fin r → PrescribedTree (n+r)) (a b : (d : Fin r) → (Target d).Leaf) :
    (∑ d ∈ U, targetContractionChangeSq (Target d) T (a d) (b d)
      (productStemMeanAt C r d.succ T f) (productStemMeanAt C r d.castSucc T f))/(L:ℝ) ≤
      4*(Fintype.card ι:ℝ)^2/(L:ℝ) := by
  have h : (∑ d ∈ U, targetContractionChangeSq (Target d) T (a d) (b d)
      (productStemMeanAt C r d.succ T f) (productStemMeanAt C r d.castSucc T f))/(L:ℝ) ≤
      (∑ d ∈ U, 4*((∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ)))/(L:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro d hd
    have hh := targetContractionChangeSq_le (Target d) T (a d) (b d)
      (productStemMeanAt C r d.succ T f) (productStemMeanAt C r d.castSucc T f)
      (productStemMeanAt_bound C r d.succ T f hf)
      (productStemMeanAt_bound C r d.castSucc T f hf)
    rw [productStemMeanAt_spatial_increment] at hh
    exact hh
  apply h.trans
  rw [← Finset.mul_sum]
  calc
    _ = 4*((∑ d ∈ U, (∑ j : Fin N, productStemIncrementSq C r T (fun x => f x j) d)/(N:ℝ))/(L:ℝ)) := by ring
    _ ≤ 4*((Fintype.card ι:ℝ)^2/(L:ℝ)) := mul_le_mul_of_nonneg_left
      (averaged_productStemIncrement_spatial_le C r L U T f hf) (by norm_num)
    _ = _ := by ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
