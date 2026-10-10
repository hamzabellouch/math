import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterPairTrace

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairMarginal (φ : Fin n → α → ℂ) (j k : Fin n) (z : α × α) : ℝ :=
  if j ≠ k then (n.factorial : ℝ)⁻¹ *
    ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ) else 0

lemma slaterPairMarginal_sum {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (z : α × α) :
    (∑ j : Fin n, ∑ k : Fin n, slaterPairMarginal (μ := μ) φ j k z) =
      (∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2) -
        ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2 := by
  have he (j k : Fin n) : slaterPairMarginal (μ := μ) φ j k z =
      (n.factorial : ℝ)⁻¹ * (if j ≠ k then
        ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
          ∂Measure.pi (fun _ : SlaterPairRest j k => μ) else 0) := by
    unfold slaterPairMarginal
    split_ifs <;> simp only [mul_zero]
  simp_rw [he, ← Finset.mul_sum]
  rw [slaterPairSliceRaw_sum_integral hφ ho, ← mul_assoc,
    inv_mul_cancel₀ (show (n.factorial:ℝ) ≠ 0 by exact_mod_cast n.factorial_ne_zero), one_mul]

omit [SigmaFinite μ] in
lemma slaterPairMarginal_nonneg (φ : Fin n → α → ℂ) (j k : Fin n) (z : α × α) :
    0 ≤ slaterPairMarginal (μ := μ) φ j k z := by
  unfold slaterPairMarginal
  split_ifs
  · exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  · rfl

lemma slaterPairMarginal_observable_integrable {φ : Fin n → α → ℂ}
    {j k : Fin n} (hjk : j ≠ k) (w : α × α → ℝ)
    (hi : Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ)) :
    Integrable (fun z => w z * slaterPairMarginal (μ := μ) φ j k z) (μ.prod μ) := by
  have mp := (slaterPairSplit_preserving (μ := μ) hjk).symm
  have h := (mp.integrable_comp_of_integrable hi).integral_prod_left
  apply h.congr
  filter_upwards [] with z
  rcases z with ⟨u,v⟩
  simp only [Function.comp_def, slaterPairSplit_symm_apply_left,
    slaterPairSplit_symm_apply_right, slater_pair_split_norm_sq, integral_const_mul,
    slaterPairMarginal, ite_eq_left hjk]

theorem slater_two_body {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (w : α × α → ℝ)
    (hi : ∀ j k : Fin n, j ≠ k →
      Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
        (Measure.pi fun _ : Fin n => μ)) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      (∫ x, w (x j,x k) * ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) else 0) =
      ∫ z, w z * ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2) -
        ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2) ∂μ.prod μ := by
  have hm (j k : Fin n) :
      Integrable (fun z => w z * slaterPairMarginal (μ := μ) φ j k z) (μ.prod μ) := by
    by_cases hjk : j ≠ k
    · exact slaterPairMarginal_observable_integrable hjk w (hi j k hjk)
    · simp [slaterPairMarginal, hjk]
  have he (j k : Fin n) :
      (if j ≠ k then (∫ x, w (x j,x k) * ‖slater φ x‖^2
        ∂Measure.pi (fun _ : Fin n => μ)) else 0) =
      ∫ z, w z * slaterPairMarginal (μ := μ) φ j k z ∂μ.prod μ := by
    by_cases hjk : j ≠ k
    · simp only [ite_eq_left hjk, slaterPairMarginal]
      exact slater_pair_observable hjk w (hi j k hjk)
    · simp only [ite_eq_right hjk, slaterPairMarginal, mul_zero, integral_zero]
  simp_rw [he]
  simp_rw [← integral_finsetSum _ (fun k _ => hm _ k)]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hm j k))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp_rw [← Finset.mul_sum]
  rw [slaterPairMarginal_sum hφ ho]

theorem slater_two_body_le_direct {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (w : α × α → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hi : ∀ j k : Fin n, j ≠ k →
      Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
        (Measure.pi fun _ : Fin n => μ))
    (hd : Integrable (fun z => w z *
      ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2))) (μ.prod μ)) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      (∫ x, w (x j,x k) * ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) else 0) ≤
      ∫ z, w z * ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2)) ∂μ.prod μ := by
  rw [slater_two_body hφ ho w hi]
  have hn : ∀ z, 0 ≤ w z * ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2) -
        ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2) := by
    intro z
    rw [← slaterPairMarginal_sum hφ ho]
    exact mul_nonneg (hw z) (Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => slaterPairMarginal_nonneg (μ := μ) φ j k z)))
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall hn) hd
    (Filter.Eventually.of_forall (fun z =>
      mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (hw z)))

end Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterCoordinate (φ ψ : Fin n → α → ℂ) (j : Fin n) (x : Fin n → α) : ℂ :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ * slaterCoordinateRaw φ ψ j x

lemma memLp_slaterCoordinate {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (j : Fin n) :
    MemLp (slaterCoordinate φ ψ j) 2 (Measure.pi fun _ : Fin n => μ) :=
  (memLp_slaterCoordinateRaw hφ hψ j).const_mul _

lemma slaterCoordinate_sum_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0) :
    (∑ j : Fin n, ∫ x, ‖slaterCoordinate φ ψ j x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) = ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ := by
  simp only [slaterCoordinate, norm_mul, mul_pow, integral_const_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)]
  rw [← Finset.mul_sum, slaterCoordinateRaw_sum_norm_sq_integral hφ hψ ho,
    ← mul_assoc, inv_mul_cancel₀ (show (n.factorial:ℝ) ≠ 0 by exact_mod_cast n.factorial_ne_zero),
    one_mul]

omit [MeasurableSpace α] in
lemma slaterCoordinateTensor_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterCoordinateTensor φ (fun i t => b t * φ i t) j σ x =
      b (x j) * slaterTensor φ σ x := by
  unfold slaterCoordinateTensor slaterTensor
  have he (i : Fin n) :
      (if i=j then (fun k t => b t * φ k t) else φ) (σ i) (x i) =
      (if i=j then b (x j) else 1) * φ (σ i) (x i) := by
    by_cases hij : i=j
    · subst i; simp
    · simp only [ite_eq_right hij, one_mul]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

omit [MeasurableSpace α] in
lemma slaterCoordinateRaw_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (x : Fin n → α) :
    slaterCoordinateRaw φ (fun i t => b t * φ i t) j x = b (x j) * slaterRaw φ x := by
  simp only [slaterCoordinateRaw, slaterCoordinateTensor_mul, slaterRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [MeasurableSpace α] in
lemma slaterCoordinate_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (x : Fin n → α) :
    slaterCoordinate φ (fun i t => b t * φ i t) j x = b (x j) * slater φ x := by
  rw [slaterCoordinate, slaterCoordinateRaw_mul, slater]
  ring

lemma slater_local_squares {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (b : α → ℂ) (hb : ∀ i, MemLp (fun t => b t * φ i t) 2 μ) :
    (∫ x, (∑ j : Fin n, ‖b (x j)‖^2) * ‖slater φ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ i, ∫ t, ‖b t‖^2 * ‖φ i t‖^2 ∂μ := by
  have hi (j : Fin n) : Integrable (fun x => ‖b (x j)‖^2 * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ) := by
    simpa only [slaterCoordinate_mul, norm_mul, mul_pow] using
      (memLp_slaterCoordinate hφ hb j).norm.integrable_sq
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simpa only [slaterCoordinate_mul, norm_mul, mul_pow] using
    slaterCoordinate_sum_norm_sq_integral hφ hb ho

lemma slater_nonnegative_potential {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (V : α → ℝ) (hV : ∀ t, 0 ≤ V t)
    (hv : ∀ i, MemLp (fun t => (Real.sqrt (V t) : ℂ) * φ i t) 2 μ) :
    (∫ x, (∑ j : Fin n, V (x j)) * ‖slater φ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ i, ∫ t, V t * ‖φ i t‖^2 ∂μ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hV _)] using
    slater_local_squares hφ ho (fun t => (Real.sqrt (V t) : ℂ)) hv

end CoulombAtom

end

end OAI
