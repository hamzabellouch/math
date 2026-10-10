import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterPairAlgebra

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairContraction (φ : Fin n → α → ℂ) (i l : Fin n) (u v : α) : ℂ :=
  conj (φ i u * φ l v) * (φ i u * φ l v) -
    conj (φ i u * φ l v) * (φ l u * φ i v)

omit [MeasurableSpace α] in
lemma slaterPairContraction_self (φ : Fin n → α → ℂ) (i : Fin n) (u v : α) :
    slaterPairContraction φ i i u v = 0 := by
  simp only [slaterPairContraction, sub_self]

omit [MeasurableSpace α] in
lemma slaterPairAmplitude_contraction (φ : Fin n → α → ℂ) (j k : Fin n)
    (σ : Equiv.Perm (Fin n)) (u v : α) :
    conj (slaterPairAmplitude φ j k σ u v) * slaterPairAmplitude φ j k σ u v -
      conj (slaterPairAmplitude φ j k σ u v) *
        slaterPairAmplitude φ j k (σ * Equiv.swap j k) u v =
      slaterPairContraction φ (σ j) (σ k) u v := by
  simp only [slaterPairAmplitude, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, slaterPairContraction]

omit [MeasurableSpace α] in
lemma slaterPairContraction_sum_of_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n))
    (u v : α) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      slaterPairContraction φ (σ j) (σ k) u v else 0) =
      ∑ i : Fin n, ∑ l : Fin n, slaterPairContraction φ i l u v := by
  have he (j k : Fin n) : (if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0) =
      slaterPairContraction φ (σ j) (σ k) u v := by
    by_cases h : j=k
    · subst k; simp only [ne_eq, not_true_eq_false, ite_false, slaterPairContraction_self]
    · rw [ite_eq_left h]
  simp_rw [he]
  calc
    _ = ∑ j : Fin n, ∑ l : Fin n, slaterPairContraction φ (σ j) l u v := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp σ (fun l => slaterPairContraction φ (σ j) l u v)
    _ = _ := Equiv.sum_comp σ (fun i => ∑ l : Fin n, slaterPairContraction φ i l u v)

omit [MeasurableSpace α] in
lemma slaterPairContraction_sum (φ : Fin n → α → ℂ) (u v : α) :
    (∑ i : Fin n, ∑ l : Fin n, slaterPairContraction φ i l u v) =
      (Complex.ofReal ((∑ i : Fin n, ‖φ i u‖^2) * (∑ i : Fin n, ‖φ i v‖^2) -
        ‖∑ i : Fin n, φ i u * conj (φ i v)‖^2)) := by
  have hnorm (z : ℂ) : Complex.ofReal (‖z‖^2) = conj z * z := by
    simpa only [Complex.sq_norm] using Complex.normSq_eq_conj_mul_self (z := z)
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum, hnorm]
  simp only [slaterPairContraction, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_mul]
    ring
  · simp only [map_sum, map_mul, starRingEnd_self_apply]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring

lemma slaterPairSliceRaw_sum_integral {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (u v : α) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
        ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) else 0) =
      (n.factorial : ℝ) *
        ((∑ i : Fin n, ‖φ i u‖^2) * (∑ i : Fin n, ‖φ i v‖^2) -
          ‖∑ i : Fin n, φ i u * conj (φ i v)‖^2) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  have he (j k : Fin n) :
      Complex.ofReal (if j ≠ k then (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
        ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) else 0) =
      ∑ σ : Equiv.Perm (Fin n), if j ≠ k then
        slaterPairContraction φ (σ j) (σ k) u v else 0 := by
    by_cases hjk : j ≠ k
    · simp only [ite_eq_left hjk]
      rw [slaterPairSliceRaw_norm_sq_integral hφ ho hjk]
      simp_rw [slaterPairAmplitude_contraction]
    · simp only [ite_eq_right hjk, Complex.ofReal_zero, Finset.sum_const_zero]
  calc
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact he j k
    _ = ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n,
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n, ∑ k : Fin n,
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [slaterPairContraction_sum_of_perm, slaterPairContraction_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

omit [MeasurableSpace α] in
lemma slaterTensor_pair (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n))
    {j k : Fin n} (hjk : j ≠ k) (x : Fin n → α) :
    slaterTensor φ σ x = slaterPairAmplitude φ j k σ (x j) (x k) *
      slaterRestTensor φ j k σ (fun i => x i) := by
  classical
  unfold slaterTensor slaterPairAmplitude slaterRestTensor
  have hk : k ∈ (Finset.univ : Finset (Fin n)).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ hk, ← mul_assoc]
  congr 1
  exact Finset.prod_subtype _ (fun i => by simp [and_comm]) _

lemma slaterRaw_pair_split (φ : Fin n → α → ℂ) {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    slaterRaw φ ((slaterPairSplit hjk).symm ((u,v),y)) =
      slaterPairSliceRaw φ j k u v y := by
  unfold slaterRaw slaterPairSliceRaw
  apply Finset.sum_congr rfl
  intro σ _
  rw [slaterTensor_pair φ σ hjk, slaterPairSplit_symm_apply_left,
    slaterPairSplit_symm_apply_right]
  simp only [slaterRestTensor, slaterPairSplit_symm_apply_rest]
  ring

lemma slater_pair_split_norm_sq (φ : Fin n → α → ℂ) {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    ‖slater φ ((slaterPairSplit hjk).symm ((u,v),y))‖^2 =
      (n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k u v y‖^2 := by
  simp only [slater, slaterRaw_pair_split, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)]

lemma slater_pair_observable {φ : Fin n → α → ℂ} {j k : Fin n} (hjk : j ≠ k)
    (w : α × α → ℝ)
    (hi : Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ)) :
    (∫ x, w (x j,x k) * ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, w z * ((n.factorial : ℝ)⁻¹ *
        ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
          ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) ∂μ.prod μ := by
  have mp := (slaterPairSplit_preserving (μ := μ) hjk).symm
  have he : (fun z : (α×α) × (SlaterPairRest j k → α) =>
      w ((slaterPairSplit hjk).symm z j,(slaterPairSplit hjk).symm z k) *
        ‖slater φ ((slaterPairSplit hjk).symm z)‖^2) =
      (fun z => w z.1 * ((n.factorial : ℝ)⁻¹ *
        ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2)) := by
    funext ⟨⟨u,v⟩,y⟩
    simp only [slaterPairSplit_symm_apply_left,
      slaterPairSplit_symm_apply_right, slater_pair_split_norm_sq]
  have hs : Integrable (fun z : (α×α) × (SlaterPairRest j k → α) =>
      w z.1 * ((n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2))
      ((μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ)) := by
    simpa only [Function.comp_def, he] using mp.integrable_comp_of_integrable hi
  calc
    _ = ∫ z : (α×α) × (SlaterPairRest j k → α),
        w z.1 * ((n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2)
        ∂(μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ) := by
      rw [← he]
      exact (mp.integral_comp' (fun x => w (x j,x k) * ‖slater φ x‖^2)).symm
    _ = _ := by
      rw [integral_prod _ hs]
      simp only [integral_const_mul]

end CoulombAtom

end

end OAI
