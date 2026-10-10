import OAI.Analysis.CoulombRadii.FieldAnalysis.SlotTensor
import OAI.Analysis.CoulombRadii.FieldAnalysis.TwoBodyTensorIntegrable

namespace OAI

/-! Mixed determinant matrix elements for different occupied orbital
families. Every coefficient is an actual integral; the remaining finite
permutation sums are precisely the minors needed in Fock compression. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.MixedSlater
open Coulomb

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {n : ℕ}

lemma determinant_overlap_integral (v u : Fin n → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : ∀ i, MemLp (u i) 2 μ) :
    (∫ x : Fin n → A, star (determinantWave v x) * determinantWave u x
      ∂(Measure.pi fun _ => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∏ i, ∫ a, star (v (p i) a) * u (q i) a ∂μ := by
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → A => star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (star (∏ i, v (p i) (x i)) * ∏ i, u (q i) (x i))) (Measure.pi fun _ => μ) :=
    ((scalarTensor_memLp v hv p).star.integrable_mul (scalarTensor_memLp u hu q)).const_mul _
  simp_rw [determinant_bilinear_expansion]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul]
  congr 1
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod
    (f := fun i a => star (v (p i) a) * u (q i) a) (μ := fun _ => μ)

lemma oneBodyTensor_integrable (v u : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : ∀ i, MemLp (u i) 2 μ)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * u j a)) μ)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    Integrable (fun x : Fin n → A => w (x i) *
      (star (∏ j, v (p j) (x j)) * ∏ j, u (q j) (x j))) (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact weighted_tensor_integrable (fun j a => star (v (p j) a) * u (q j) a) w i
    (fun j => (hv (p j)).star.integrable_mul (hu (q j))) (hw _ _)

lemma oneBodyTensor_integral (v u : Fin n → A → ℂ) (w : A → ℂ)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) *
      (star (∏ j, v (p j) (x j)) * ∏ j, u (q j) (x j)) ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * (star (v (p i) a) * u (q i) a) ∂μ) *
        ∏ j ∈ Finset.univ.erase i, ∫ a, star (v (p j) a) * u (q j) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact weighted_tensor_integral (fun j a => star (v (p j) a) * u (q j) a) w i

lemma twoBodyTensor_integrable (v u : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : ∀ i, MemLp (u i) 2 μ)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * u c xy.1) * (star (v b xy.2) * u d xy.2))) (μ.prod μ))
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, u (q k) (x k))) (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact pair_weight_tensor_integrable i j hij (fun k a => star (v (p k) a) * u (q k) a) w
    (fun k => (hv (p k)).star.integrable_mul (hu (q k))) (hw _ _ _ _)

lemma twoBodyTensor_integral (v u : Fin n → A → ℂ) (w : A → A → ℂ)
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Fin n → A, w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, u (q k) (x k)) ∂(Measure.pi fun _ => μ)) =
      (∫ xy : A × A, w xy.1 xy.2 *
        ((star (v (p i) xy.1) * u (q i) xy.1) * (star (v (p j) xy.2) * u (q j) xy.2))
          ∂(μ.prod μ)) * ∏ k ∈ (Finset.univ.erase i).erase j,
            ∫ a, star (v (p k) a) * u (q k) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact pair_weight_tensor_integral i j hij (fun k a => star (v (p k) a) * u (q k) a) w

lemma slotTensor_integral (v d u e : Fin n → A → ℂ)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x, star (slotTensor v d p i x) * slotTensor u e q i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      (∫ a, star (d (p i) a) * e (q i) a ∂μ) *
        ∏ j ∈ Finset.univ.erase i, ∫ a, star (v (p j) a) * u (q j) a ∂μ := by
  simp only [slotTensor, star_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (f := fun j a =>
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then e (q j) a else u (q j) a)) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∫ a,
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then e (q j) a else u (q j) a) ∂μ) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

omit [MeasurableSpace A] in
lemma slotDeterminant_expansion (v d u e : Fin n → A → ℂ) (i : Fin n) (x : Fin n → A) :
    star (slotDeterminant v d i x) * slotDeterminant u e i x =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          (star (slotTensor v d p i x) * slotTensor u e q i x) := by
  simp only [slotDeterminant, star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma slotDeterminant_integral (v d u e : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (hu : ∀ a, MemLp (u a) 2 μ) (he : ∀ a, MemLp (e a) 2 μ) (i : Fin n) :
    (∫ x, star (slotDeterminant v d i x) * slotDeterminant u e i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ((∫ a, star (d (p i) a) * e (q i) a ∂μ) *
            ∏ j ∈ Finset.univ.erase i, ∫ a, star (v (p j) a) * u (q j) a ∂μ) := by
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → A => star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (star (slotTensor v d p i x) * slotTensor u e q i x)) (Measure.pi fun _ => μ) :=
    ((slotTensor_memLp v d hv hd p i).star.integrable_mul
      (slotTensor_memLp u e hu he q i)).const_mul _
  simp_rw [slotDeterminant_expansion]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul, slotTensor_integral]

omit [MeasurableSpace A] in
lemma determinant_oneBody_expansion (v u : Fin n → A → ℂ) (w : A → ℂ) (x : Fin n → A) :
    (∑ i, w (x i)) * (star (determinantWave v x) * determinantWave u x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, u (q j) (x j)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma determinant_oneBody_integral (v u : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : ∀ i, MemLp (u i) 2 μ)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * u j a)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i)) *
      (star (determinantWave v x) * determinantWave u x) ∂(Measure.pi fun _ => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, (∫ a, w a * (star (v (p i) a) * u (q i) a) ∂μ) *
            ∏ j ∈ Finset.univ.erase i, ∫ a, star (v (p j) a) * u (q j) a ∂μ := by
  let F (p q : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, u (q j) (x j))
  let c (p q : Equiv.Perm (Fin n)) : ℂ := star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ i, F p q i x) (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => oneBodyTensor_integrable v u w hv hu hw p q i)
  have hj (p : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ q, c p q * ∑ i, F p q i x)
      (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun q _ => (hi p q).const_mul (c p q))
  simp_rw [determinant_oneBody_expansion]
  rw [integral_finsetSum _ (fun p _ => hj p)]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul (c p q))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul, integral_finsetSum _
    (fun i _ => oneBodyTensor_integrable v u w hv hu hw p q i)]
  simp only [oneBodyTensor_integral, c]

omit [MeasurableSpace A] in
lemma determinant_twoBody_expansion (v u : Fin n → A → ℂ) (w : A → A → ℂ) (x : Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave u x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j) *
            (star (∏ k, v (p k) (x k)) * ∏ k, u (q k) (x k)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma determinant_twoBody_integral (v u : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : ∀ i, MemLp (u i) 2 μ)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * u c xy.1) * (star (v b xy.2) * u d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave u x) ∂(Measure.pi fun _ => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            (∫ xy : A × A, w xy.1 xy.2 *
              ((star (v (p i) xy.1) * u (q i) xy.1) *
                (star (v (p j) xy.2) * u (q j) xy.2)) ∂(μ.prod μ)) *
              ∏ k ∈ (Finset.univ.erase i).erase j,
                ∫ a, star (v (p k) a) * u (q k) a ∂μ := by
  let F (p q : Equiv.Perm (Fin n)) (i j : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) (x j) * (star (∏ k, v (p k) (x k)) * ∏ k, u (q k) (x k))
  let c (p q : Equiv.Perm (Fin n)) : ℂ := star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x) (Measure.pi fun _ => μ) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j hj =>
      twoBodyTensor_integrable v u w hv hu hw p q i j (Finset.mem_erase.mp hj).1.symm))
  have hj (p : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x)
      (Measure.pi fun _ => μ) := integrable_finsetSum _ (fun q _ => (hi p q).const_mul _)
  calc
    _ = ∫ x : Fin n → A, ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x
        ∂(Measure.pi fun _ => μ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact determinant_twoBody_expansion v u w x
    _ = ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x : Fin n → A, F p q i j x ∂(Measure.pi fun _ => μ) := by
      rw [integral_finsetSum _ (fun p _ => hj p)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j hj => twoBodyTensor_integrable v u w hv hu hw p q i j (Finset.mem_erase.mp hj).1.symm))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j hj =>
        twoBodyTensor_integrable v u w hv hu hw p q i j (Finset.mem_erase.mp hj).1.symm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact twoBodyTensor_integral v u w p q i j (Finset.mem_erase.mp hj).1.symm

end ContinuumCoulomb.MixedSlater

end

end OAI
