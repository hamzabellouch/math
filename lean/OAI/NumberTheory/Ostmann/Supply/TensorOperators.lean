import OAI.NumberTheory.Ostmann.Supply.BivariateTruncation

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorOperators
open scoped BigOperators TensorProduct

structure FiniteHilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [finiteDimensional : FiniteDimensional ℂ carrier]

attribute [instance] FiniteHilbertSpace.normedAddCommGroup
  FiniteHilbertSpace.innerProductSpace FiniteHilbertSpace.finiteDimensional

instance : CoeSort FiniteHilbertSpace Type := ⟨FiniteHilbertSpace.carrier⟩

namespace FiniteHilbertSpace

def of (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : FiniteHilbertSpace := ⟨E⟩

def tensor (E F : FiniteHilbertSpace) : FiniteHilbertSpace :=
  of (E ⊗[ℂ] F)

instance (E : FiniteHilbertSpace) : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

end FiniteHilbertSpace

def tensorSpace (E : ℕ → FiniteHilbertSpace) : ℕ → FiniteHilbertSpace
  | 0 => FiniteHilbertSpace.of ℂ
  | n + 1 => FiniteHilbertSpace.tensor (tensorSpace E n) (E n)

def tensorOp {E F : ℕ → FiniteHilbertSpace} (T : ∀ i, E i →L[ℂ] F i) :
    (n : ℕ) → tensorSpace E n →L[ℂ] tensorSpace F n
  | 0 => ContinuousLinearMap.id ℂ ℂ
  | n + 1 => TensorProduct.mapL (tensorOp T n) (T n)

def pureTensor {E : ℕ → FiniteHilbertSpace} (v : ∀ i, E i) :
    (n : ℕ) → tensorSpace E n
  | 0 => (1 : ℂ)
  | n + 1 => pureTensor v n ⊗ₜ[ℂ] v n

theorem tensorOp_pureTensor {E F : ℕ → FiniteHilbertSpace}
    (T : ∀ i, E i →L[ℂ] F i) (v : ∀ i, E i) (n : ℕ) :
    tensorOp T n (pureTensor v n) = pureTensor (fun i => T i (v i)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.mapL (tensorOp T n) (T n) (pureTensor v n ⊗ₜ[ℂ] v n) = _
    rw [TensorProduct.mapL_tmul, ih]
    rfl

theorem norm_tensorOp_le {E F : ℕ → FiniteHilbertSpace}
    (T : ∀ i, E i →L[ℂ] F i) (n : ℕ) :
    ‖tensorOp T n‖ ≤ ∏ i ∈ Finset.range n, ‖T i‖ := by
  induction n with
  | zero =>
    change ‖ContinuousLinearMap.id ℂ ℂ‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact (TensorProduct.norm_mapL_le (tensorOp T n) (T n)).trans
      (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

theorem norm_tensorOp_le_of_local {E F : ℕ → FiniteHilbertSpace}
    (T : ∀ i, E i →L[ℂ] F i) (M : ℕ → ℝ) (n : ℕ)
    (hM : ∀ i < n, ‖T i‖ ≤ M i) :
    ‖tensorOp T n‖ ≤ ∏ i ∈ Finset.range n, M i := by
  apply (norm_tensorOp_le T n).trans
  exact Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => hM i (Finset.mem_range.mp hi))

theorem norm_pureTensor {E : ℕ → FiniteHilbertSpace} (v : ∀ i, E i) (n : ℕ) :
    ‖pureTensor v n‖ = ∏ i ∈ Finset.range n, ‖v i‖ := by
  induction n with
  | zero =>
    change ‖(1 : ℂ)‖ = 1
    exact norm_one
  | succ n ih =>
    change ‖pureTensor v n ⊗ₜ[ℂ] v n‖ = _
    rw [TensorProduct.norm_tmul, ih, Finset.prod_range_succ]

theorem pureTensor_inner {E : ℕ → FiniteHilbertSpace}
    (v w : ∀ i, E i) (n : ℕ) :
    inner ℂ (pureTensor v n) (pureTensor w n) =
      ∏ i ∈ Finset.range n, inner ℂ (v i) (w i) := by
  induction n with
  | zero =>
    change inner ℂ (1 : ℂ) 1 = 1
    simp
  | succ n ih =>
    change inner ℂ (pureTensor v n ⊗ₜ[ℂ] v n) (pureTensor w n ⊗ₜ[ℂ] w n) = _
    rw [TensorProduct.inner_tmul, ih, Finset.prod_range_succ]

open scoped BigOperators TensorProduct
open BivariateTruncation

section Evaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def evalLinearMap (u v : ℂ) : ((ℕ × ℕ) →₀ E) →ₗ[ℂ] E :=
  Finsupp.lsum ℂ (fun ij => (u ^ ij.1 * v ^ ij.2) • LinearMap.id)

@[simp] lemma evalLinearMap_apply (u v : ℂ) (c : (ℕ × ℕ) →₀ E) :
    evalLinearMap u v c = eval c u v := rfl

@[simp] lemma eval_single (ij : ℕ × ℕ) (a : E) (u v : ℂ) :
    eval (Finsupp.single ij a) u v = (u ^ ij.1 * v ^ ij.2) • a := by
  change evalLinearMap (E := E) u v (Finsupp.single ij a) = _
  unfold evalLinearMap
  rw [Finsupp.lsum_single]
  rfl

lemma eval_sum {α : Type*} (s : Finset α) (c : α → (ℕ × ℕ) →₀ E) (u v : ℂ) :
    eval (∑ x ∈ s, c x) u v = ∑ x ∈ s, eval (c x) u v := by
  exact map_sum (evalLinearMap (E := E) u v) c s

end Evaluation

section Binary
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mapL_sum_left {α : Type*} (s : Finset α) (f : α → E →L[ℂ] F) (g : G →L[ℂ] H) :
    TensorProduct.mapL (∑ x ∈ s, f x) g = ∑ x ∈ s, TensorProduct.mapL (f x) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, TensorProduct.mapL_add_left, ih]

lemma mapL_sum_right {α : Type*} (s : Finset α) (f : E →L[ℂ] F) (g : α → G →L[ℂ] H) :
    TensorProduct.mapL f (∑ x ∈ s, g x) = ∑ x ∈ s, TensorProduct.mapL f (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, TensorProduct.mapL_add_right, ih]

def tensorPolynomial (c : (ℕ × ℕ) →₀ (E →L[ℂ] F))
    (d : (ℕ × ℕ) →₀ (G →L[ℂ] H)) :
    (ℕ × ℕ) →₀ ((E ⊗[ℂ] G) →L[ℂ] (F ⊗[ℂ] H)) :=
  ∑ ij ∈ c.support, ∑ kl ∈ d.support,
    Finsupp.single (ij.1 + kl.1, ij.2 + kl.2) (TensorProduct.mapL (c ij) (d kl))

theorem eval_tensorPolynomial (c : (ℕ × ℕ) →₀ (E →L[ℂ] F))
    (d : (ℕ × ℕ) →₀ (G →L[ℂ] H)) (u v : ℂ) :
    eval (tensorPolynomial c d) u v = TensorProduct.mapL (eval c u v) (eval d u v) := by
  simp only [tensorPolynomial, eval_sum, eval_single]
  rw [eval, mapL_sum_left]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [eval, mapL_sum_right]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [TensorProduct.mapL_smul_left]
  rw [TensorProduct.mapL_smul_right]
  apply ContinuousLinearMap.ext
  intro z
  simp only [smul_apply]
  rw [smul_smul]
  congr 1
  simp only [pow_add]
  ring

end Binary

def tensorFamilyPolynomial {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) :
    (n : ℕ) → (ℕ × ℕ) →₀ (tensorSpace E n →L[ℂ] tensorSpace F n)
  | 0 => Finsupp.single (0,0) (ContinuousLinearMap.id ℂ ℂ)
  | n + 1 => tensorPolynomial (tensorFamilyPolynomial c n) (c n)

theorem eval_tensorFamilyPolynomial {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) (n : ℕ) (u v : ℂ) :
    BivariateTruncation.eval (tensorFamilyPolynomial c n) u v =
      tensorOp (fun i => BivariateTruncation.eval (c i) u v) n := by
  induction n with
  | zero =>
    change BivariateTruncation.eval
      (Finsupp.single (0,0) (ContinuousLinearMap.id ℂ ℂ)) u v = ContinuousLinearMap.id ℂ ℂ
    simp only [eval_single, pow_zero, one_mul, one_smul]
  | succ n ih =>
    change BivariateTruncation.eval (tensorPolynomial (tensorFamilyPolynomial c n) (c n)) u v =
      TensorProduct.mapL (tensorOp (fun i => BivariateTruncation.eval (c i) u v) n)
        (BivariateTruncation.eval (c n) u v)
    rw [eval_tensorPolynomial, ih]

theorem norm_eval_tensorFamilyPolynomial_le {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) (n : ℕ) (u v : ℂ) :
    ‖BivariateTruncation.eval (tensorFamilyPolynomial c n) u v‖ ≤
      ∏ i ∈ Finset.range n, ‖BivariateTruncation.eval (c i) u v‖ := by
  rw [eval_tensorFamilyPolynomial]
  exact norm_tensorOp_le _ _

theorem norm_eval_tensorFamilyPolynomial_le_of_local {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) (M : ℕ → ℝ) (n : ℕ) (u v : ℂ)
    (hM : ∀ i < n, ‖BivariateTruncation.eval (c i) u v‖ ≤ M i) :
    ‖BivariateTruncation.eval (tensorFamilyPolynomial c n) u v‖ ≤
      ∏ i ∈ Finset.range n, M i := by
  rw [eval_tensorFamilyPolynomial]
  exact norm_tensorOp_le_of_local _ M n hM

theorem tensorFamily_coefficient_norm_le {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) (M : ℕ → ℝ) (n : ℕ)
    {r : ℝ} (hr : 0 < r)
    (hM : ∀ k < n, ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r →
      ‖BivariateTruncation.eval (c k) u v‖ ≤ M k) (i j : ℕ) :
    ‖tensorFamilyPolynomial c n (i,j)‖ ≤ (∏ k ∈ Finset.range n, M k) / r ^ (i + j) := by
  apply BivariateTruncation.coefficient_norm_le _ hr
  intro u v hu hv
  exact norm_eval_tensorFamilyPolynomial_le_of_local c M n u v
    (fun k hk => hM k hk u v hu hv)

theorem tensorFamily_rectangular_error_le {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (E i →L[ℂ] F i)) (M : ℕ → ℝ) (n : ℕ)
    {r : ℝ} (hr : 1 < r)
    (hM : ∀ k < n, ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r →
      ‖BivariateTruncation.eval (c k) u v‖ ≤ M k) (K : ℕ) :
    ‖BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K -
      tensorOp (fun k => BivariateTruncation.eval (c k) 1 1) n‖ ≤
      2 * (∏ k ∈ Finset.range n, M k) * (r⁻¹) ^ K / (1 - r⁻¹) ^ 2 := by
  rw [← eval_tensorFamilyPolynomial c n 1 1]
  apply BivariateTruncation.rectangularTruncation_error_le _ hr
  intro u v hu hv
  exact norm_eval_tensorFamilyPolynomial_le_of_local c M n u v
    (fun k hk => hM k hk u v hu hv)

section LocalProjection
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma eval_add (c d : (ℕ × ℕ) →₀ (E →L[ℂ] F)) (u v : ℂ) :
    BivariateTruncation.eval (c + d) u v =
      BivariateTruncation.eval c u v + BivariateTruncation.eval d u v := by
  exact map_add (evalLinearMap (E := E →L[ℂ] F) u v) c d

def projectionPolynomial (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : E →L[ℂ] F) :
    (ℕ × ℕ) →₀ (E →L[ℂ] F) :=
  Finsupp.single (0,0) (((ContinuousLinearMap.id ℂ F - Q) ∘L L) ∘L (ContinuousLinearMap.id ℂ E - P)) +
  Finsupp.single (1,0) (((ContinuousLinearMap.id ℂ F - Q) ∘L L) ∘L P) +
  Finsupp.single (0,1) ((Q ∘L L) ∘L (ContinuousLinearMap.id ℂ E - P)) +
  Finsupp.single (1,1) ((Q ∘L L) ∘L P)

theorem eval_projectionPolynomial (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (L : E →L[ℂ] F) (u v : ℂ) :
    BivariateTruncation.eval (projectionPolynomial P Q L) u v =
      ((ContinuousLinearMap.id ℂ F - Q + v • Q) ∘L L) ∘L
        (ContinuousLinearMap.id ℂ E - P + u • P) := by
  simp only [projectionPolynomial, eval_add, eval_single, pow_zero, pow_one,
    one_mul, mul_one, one_smul]
  ext x
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul, smul_add, smul_smul]
  rw [mul_comm u v]
  abel

lemma eval_projectionPolynomial_one (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (L : E →L[ℂ] F) : BivariateTruncation.eval (projectionPolynomial P Q L) 1 1 = L := by
  rw [eval_projectionPolynomial]
  simp

theorem norm_eval_projectionPolynomial_le (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (L : E →L[ℂ] F) (u v : ℂ) :
    ‖BivariateTruncation.eval (projectionPolynomial P Q L) u v‖ ≤
      (‖ContinuousLinearMap.id ℂ F - Q‖ + ‖v‖ * ‖Q‖) * ‖L‖ *
        (‖ContinuousLinearMap.id ℂ E - P‖ + ‖u‖ * ‖P‖) := by
  rw [eval_projectionPolynomial]
  have hQ : ‖ContinuousLinearMap.id ℂ F - Q + v • Q‖ ≤
      ‖ContinuousLinearMap.id ℂ F - Q‖ + ‖v‖ * ‖Q‖ := by
    simpa only [norm_smul] using norm_add_le (ContinuousLinearMap.id ℂ F - Q) (v • Q)
  have hP : ‖ContinuousLinearMap.id ℂ E - P + u • P‖ ≤
      ‖ContinuousLinearMap.id ℂ E - P‖ + ‖u‖ * ‖P‖ := by
    simpa only [norm_smul] using norm_add_le (ContinuousLinearMap.id ℂ E - P) (u • P)
  calc
    _ ≤ ‖(ContinuousLinearMap.id ℂ F - Q + v • Q) ∘L L‖ *
        ‖ContinuousLinearMap.id ℂ E - P + u • P‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖ContinuousLinearMap.id ℂ F - Q + v • Q‖ * ‖L‖) *
        ‖ContinuousLinearMap.id ℂ E - P + u • P‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)) hP (norm_nonneg _) (by positivity)

end LocalProjection

end Ostmann.Supply.TensorOperators

end

end OAI
