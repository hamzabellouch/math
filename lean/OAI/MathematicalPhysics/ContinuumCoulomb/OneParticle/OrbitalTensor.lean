import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSlaterTensor
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTensorCompression

namespace OAI

/-! Integrals of actual finite orbital tensors, including the exact
one-body head-slot contraction. All coefficients come from the orbital
integrals; no effective matrix identity is a premise. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.OrbitalTensor
open Laughlin FockSlaterTensor

lemma delta_product {Q n : ℕ} (a b : Laughlin.Configuration n Q) :
    (∏ i, if a i = b i then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma prod_erase_zero {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∏ j ∈ Finset.univ.erase 0, f j) = ∏ j : Fin n, f j.succ := by
  classical
  let g : Fin (n + 1) → ℂ := fun j => if j = 0 then 1 else f j
  have h : (∏ j, g j) = ∏ j ∈ Finset.univ.erase 0, f j := by
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ 0)]
    simp only [g, ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    exact ite_eq_right (Finset.mem_erase.mp hj).1
  rw [← h, Fin.prod_univ_succ]
  simp only [g, ite_true, Fin.succ_ne_zero, ite_false, one_mul]

lemma head_pair_sum {Q n : ℕ} (f : Laughlin.Configuration (n + 1) Q →
    Laughlin.Configuration (n + 1) Q → ℂ) :
    (∑ a, ∑ b, f a b) = ∑ i, ∑ j, ∑ a : Laughlin.Configuration n Q,
      ∑ b : Laughlin.Configuration n Q, f (Fin.cons i a) (Fin.cons j b) := by
  rw [sum_config_cons]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sum_config_cons]
  rw [Finset.sum_comm]

private lemma prod_erase_zero_one {n : ℕ} (f : Fin (n + 2) → ℂ) :
    (∏ j ∈ (Finset.univ.erase 0).erase 1, f j) = ∏ j : Fin n, f j.succ.succ := by
  classical
  let g : Fin (n + 2) → ℂ := fun j => if j = 1 then 1 else f j
  have h : (∏ j ∈ Finset.univ.erase 0, g j) =
      ∏ j ∈ (Finset.univ.erase 0).erase 1, f j := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase 0) g (a := 1) (by simp)]
    simp only [g, ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    exact ite_eq_right (Finset.mem_erase.mp hj).1
  rw [← h, prod_erase_zero, Fin.prod_univ_succ]
  simp only [g, Fin.succ_zero_eq_one, ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro j _
  apply ite_eq_right
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_succ, Fin.val_one] at hv
  omega

lemma headTwo_pair_sum {Q n : ℕ} (f : Laughlin.Configuration (n + 2) Q →
    Laughlin.Configuration (n + 2) Q → ℂ) :
    (∑ a, ∑ b, f a b) = ∑ i, ∑ k, ∑ j, ∑ l,
      ∑ a : Laughlin.Configuration n Q, ∑ b : Laughlin.Configuration n Q,
        f (Fin.cons i (Fin.cons j a)) (Fin.cons k (Fin.cons l b)) := by
  rw [head_pair_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  exact head_pair_sum _

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {Q n : ℕ}

lemma tensorValue_memLp (v : Fin (Q + 1) → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ψ : State n Q) : MemLp (tensorValue v ψ) 2 (Measure.pi fun _ => μ) := by
  have ht (a : Laughlin.Configuration n Q) : MemLp (fun x : Fin n → A =>
      ψ a * ∏ i, v (a i) (x i)) 2 (Measure.pi fun _ => μ) := by
    simpa only [Equiv.Perm.one_apply] using
      (Coulomb.scalarTensor_memLp (fun i => v (a i)) (fun i => hv (a i))
        (1 : Equiv.Perm (Fin n))).const_mul (ψ a)
  exact memLp_finsetSum Finset.univ (fun a _ => ht a)

omit [MeasurableSpace A] in
lemma bilinear_expansion (v : Fin (Q + 1) → A → ℂ) (ψ φ : State n Q) (x : Fin n → A) :
    star (tensorValue v ψ x) * tensorValue v φ x =
      ∑ a : Laughlin.Configuration n Q, ∑ b : Laughlin.Configuration n Q,
        (star (ψ a) * φ b) * (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)) := by
  simp only [tensorValue, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma inner_integral (v : Fin (Q + 1) → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (ψ φ : State n Q) :
    (∫ x : Fin n → A, star (tensorValue v ψ x) * tensorValue v φ x
      ∂(Measure.pi fun _ => μ)) = ∑ a, star (ψ a) * φ a := by
  have ht (a b : Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a) * φ b) * (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)))
      (Measure.pi fun _ => μ) := by
    have ha := Coulomb.scalarTensor_memLp (fun i => v (a i)) (fun i => hv (a i))
      (1 : Equiv.Perm (Fin n))
    have hb := Coulomb.scalarTensor_memLp (fun i => v (b i)) (fun i => hv (b i))
      (1 : Equiv.Perm (Fin n))
    exact (ha.star.integrable_mul hb).const_mul _
  simp_rw [bilinear_expansion]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => ht a b)]
  have hI (b : Laughlin.Configuration n Q) :
      (∫ x : Fin n → A, star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)
        ∂(Measure.pi fun _ => μ)) = ∏ i, ∫ y, star (v (a i) y) * v (b i) y ∂μ := by
    simp only [star_prod, ← Finset.prod_mul_distrib]
    exact integral_fintype_prod_eq_prod (f := fun i y => star (v (a i) y) * v (b i) y)
      (μ := fun _ => μ)
  simp only [integral_const_mul, hI, ho, delta_product]
  simp

lemma head_oneBody_integral (v : Fin (Q + 1) → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j, Integrable (fun x => w x * (star (v i x) * v j x)) μ)
    (ψ φ : State (n + 1) Q) :
    (∫ x : Fin (n + 1) → A, w (x 0) *
      (star (tensorValue v ψ x) * tensorValue v φ x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, w x * (star (v i x) * v j x) ∂μ) *
        ∑ a : Laughlin.Configuration n Q, star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  have ht (a b : Laughlin.Configuration (n + 1) Q) : Integrable
      (fun x : Fin (n + 1) → A => (star (ψ a) * φ b) * (w (x 0) *
        (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)))) (Measure.pi fun _ => μ) := by
    simpa only [Equiv.Perm.one_apply] using
      (MixedSlater.oneBodyTensor_integrable (fun i => v (a i)) (fun i => v (b i)) w
        (fun i => hv (a i)) (fun i => hv (b i)) (fun i j => hw (a i) (b j))
        (1 : Equiv.Perm (Fin (n + 1))) 1 0).const_mul (star (ψ a) * φ b)
  have he (x : Fin (n + 1) → A) : w (x 0) *
      (star (tensorValue v ψ x) * tensorValue v φ x) =
      ∑ a : Laughlin.Configuration (n + 1) Q, ∑ b : Laughlin.Configuration (n + 1) Q,
        (star (ψ a) * φ b) * (w (x 0) *
          (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i))) := by
    rw [bilinear_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  simp_rw [integral_finsetSum _ (fun b _ => ht _ b), integral_const_mul]
  have hI (a b : Laughlin.Configuration (n + 1) Q) :
      (∫ x : Fin (n + 1) → A, w (x 0) *
        (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)) ∂(Measure.pi fun _ => μ)) =
      (∫ y, w y * (star (v (a 0) y) * v (b 0) y) ∂μ) *
        ∏ j ∈ Finset.univ.erase 0, ∫ y, star (v (a j) y) * v (b j) y ∂μ := by
    exact MixedSlater.oneBodyTensor_integral (fun i => v (a i)) (fun i => v (b i)) w
      (1 : Equiv.Perm (Fin (n + 1))) 1 0
  simp_rw [hI]
  simp only [ho, prod_erase_zero]
  rw [head_pair_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, delta_product]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma oneBody_CAR_compression (v : Fin (Q + 1) → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j, Integrable (fun x => w x * (star (v i x) * v j x)) μ)
    (ψ φ : State (n + 1) Q) (hψ : Laughlin.Antisymmetric ψ) (hφ : Laughlin.Antisymmetric φ) :
    (n + 1 : ℂ) * (∫ x : Fin (n + 1) → A, w (x 0) *
      (star (tensorValue v ψ x) * tensorValue v φ x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, w x * (star (v i x) * v j x) ∂μ) *
        Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n + 1) Q ψ)
          (Laughlin.Fock.create i (Laughlin.Fock.annihilate j
            (Laughlin.Fock.normalizedTensorExterior (n + 1) Q φ))) := by
  rw [head_oneBody_integral v w hv ho hw ψ φ]
  simp only [FockTensorCompression.oneBody_inner n Q ψ φ hψ hφ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

lemma head_twoBody_integral (v : Fin (Q + 1) → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j k l, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2))) (μ.prod μ))
    (ψ φ : State (n + 2) Q) :
    (∫ x : Fin (n + 2) → A, w (x 0) (x 1) *
      (star (tensorValue v ψ x) * tensorValue v φ x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2)) ∂(μ.prod μ)) *
        ∑ a : Laughlin.Configuration n Q,
          star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a)) := by
  have hij : (0 : Fin (n + 2)) ≠ 1 := by norm_num
  have ht (a b : Laughlin.Configuration (n + 2) Q) : Integrable
      (fun x : Fin (n + 2) → A => (star (ψ a) * φ b) * (w (x 0) (x 1) *
        (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)))) (Measure.pi fun _ => μ) := by
    simpa only [Equiv.Perm.one_apply] using
      (MixedSlater.twoBodyTensor_integrable (fun i => v (a i)) (fun i => v (b i)) w
        (fun i => hv (a i)) (fun i => hv (b i)) (fun i j k l => hw (a i) (a j) (b k) (b l))
        (1 : Equiv.Perm (Fin (n + 2))) 1 0 1 hij).const_mul (star (ψ a) * φ b)
  have he (x : Fin (n + 2) → A) : w (x 0) (x 1) *
      (star (tensorValue v ψ x) * tensorValue v φ x) =
      ∑ a : Laughlin.Configuration (n + 2) Q, ∑ b : Laughlin.Configuration (n + 2) Q,
        (star (ψ a) * φ b) * (w (x 0) (x 1) *
          (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i))) := by
    rw [bilinear_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  simp_rw [integral_finsetSum _ (fun b _ => ht _ b), integral_const_mul]
  have hI (a b : Laughlin.Configuration (n + 2) Q) :
      (∫ x : Fin (n + 2) → A, w (x 0) (x 1) *
        (star (∏ i, v (a i) (x i)) * ∏ i, v (b i) (x i)) ∂(Measure.pi fun _ => μ)) =
      (∫ xy : A × A, w xy.1 xy.2 *
        ((star (v (a 0) xy.1) * v (b 0) xy.1) *
          (star (v (a 1) xy.2) * v (b 1) xy.2)) ∂(μ.prod μ)) *
        ∏ j ∈ (Finset.univ.erase 0).erase 1, ∫ y, star (v (a j) y) * v (b j) y ∂μ := by
    exact MixedSlater.twoBodyTensor_integral (fun i => v (a i)) (fun i => v (b i)) w
      (1 : Equiv.Perm (Fin (n + 2))) 1 0 1 hij
  simp_rw [hI]
  simp only [ho, prod_erase_zero_one]
  rw [headTwo_pair_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.cons_one, delta_product]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma twoBody_CAR_compression (v : Fin (Q + 1) → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j k l, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2))) (μ.prod μ))
    (ψ φ : State (n + 2) Q) (hψ : Laughlin.Antisymmetric ψ) (hφ : Laughlin.Antisymmetric φ) :
    ((n + 2 : ℂ) * (n + 1 : ℂ)) * (∫ x : Fin (n + 2) → A, w (x 0) (x 1) *
      (star (tensorValue v ψ x) * tensorValue v φ x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2)) ∂(μ.prod μ)) *
        Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n + 2) Q ψ)
          (Laughlin.Fock.create i (Laughlin.Fock.create j (Laughlin.Fock.annihilate l
            (Laughlin.Fock.annihilate k (Laughlin.Fock.normalizedTensorExterior (n + 2) Q φ))))) := by
  rw [head_twoBody_integral v w hv ho hw ψ φ]
  simp only [FockTensorCompression.twoBody_inner n Q ψ φ hψ hφ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring_nf

lemma slater_oneBody_CAR_compression (v : Fin (Q + 1) → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j, Integrable (fun x => w x * (star (v i x) * v j x)) μ)
    (c d : EuclideanSpace ℂ (SlaterOccupation.Occupied Q (n + 1))) :
    (n + 1 : ℂ) * (∫ x : Fin (n + 1) → A, w (x 0) *
      (star (∑ S, c S * SlaterOccupation.wave v S x) *
        ∑ T, d T * SlaterOccupation.wave v T x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, w x * (star (v i x) * v j x) ∂μ) *
        Laughlin.Fock.occupationInner Q (∑ S, c S • Laughlin.Fock.occupationBasis Q S.val)
          (Laughlin.Fock.create i (Laughlin.Fock.annihilate j
            (∑ T, d T • Laughlin.Fock.occupationBasis Q T.val))) := by
  have h := oneBody_CAR_compression v w hv ho hw (occupationTensor c) (occupationTensor d)
    (occupationTensor_antisymmetric c) (occupationTensor_antisymmetric d)
  simpa only [tensorValue_occupationTensor, normalizedTensorExterior_occupationTensor] using h

lemma slater_twoBody_CAR_compression (v : Fin (Q + 1) → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j k l, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2))) (μ.prod μ))
    (c d : EuclideanSpace ℂ (SlaterOccupation.Occupied Q (n + 2))) :
    ((n + 2 : ℂ) * (n + 1 : ℂ)) * (∫ x : Fin (n + 2) → A, w (x 0) (x 1) *
      (star (∑ S, c S * SlaterOccupation.wave v S x) *
        ∑ T, d T * SlaterOccupation.wave v T x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v k xy.1) * (star (v j xy.2) * v l xy.2)) ∂(μ.prod μ)) *
        Laughlin.Fock.occupationInner Q (∑ S, c S • Laughlin.Fock.occupationBasis Q S.val)
          (Laughlin.Fock.create i (Laughlin.Fock.create j (Laughlin.Fock.annihilate l
            (Laughlin.Fock.annihilate k (∑ T, d T • Laughlin.Fock.occupationBasis Q T.val))))) := by
  have h := twoBody_CAR_compression v w hv ho hw (occupationTensor c) (occupationTensor d)
    (occupationTensor_antisymmetric c) (occupationTensor_antisymmetric d)
  simpa only [tensorValue_occupationTensor, normalizedTensorExterior_occupationTensor] using h

end ContinuumCoulomb.OrbitalTensor

end

end OAI
