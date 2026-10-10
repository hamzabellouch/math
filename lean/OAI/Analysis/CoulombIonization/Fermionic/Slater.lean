import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.TrialSmoothTest

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterTensor (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) : ℂ :=
  ∏ i, φ (σ i) (x i)

def slaterRaw (φ : Fin n → α → ℂ) (x : Fin n → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (((σ.sign : ℤ) : ℂ)) * slaterTensor φ σ x

omit [MeasurableSpace α] in
lemma slaterRaw_eq_det (φ : Fin n → α → ℂ) (x : Fin n → α) :
    slaterRaw φ x = Matrix.det (Matrix.of (fun i j => φ i (x j))) := by
  rw [Matrix.det_apply']
  rfl

lemma memLp_slaterTensor {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterTensor φ σ) 2 (Measure.pi fun _ : Fin n => μ) := by
  have hm : AEStronglyMeasurable (slaterTensor φ σ) (Measure.pi fun _ : Fin n => μ) := by
    unfold slaterTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hφ (σ i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : Fin n => (hφ (σ i)).norm.integrable_sq)

lemma memLp_slaterRaw {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ) :
    MemLp (slaterRaw φ) 2 (Measure.pi fun _ : Fin n => μ) :=
  memLp_finsetSum _ (fun σ _ => (memLp_slaterTensor hφ σ).const_mul _)

lemma slaterTensor_inner (φ ψ : Fin n → α → ℂ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterTensor φ σ x) * slaterTensor ψ τ x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ i, ∫ t, conj (φ (σ i) t) * ψ (τ i) t ∂μ := by
  simp only [slaterTensor, map_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i t => conj (φ (σ i) t) * ψ (τ i) t)

lemma permutations_eq_of_agree_except (σ τ : Equiv.Perm (Fin n)) (j : Fin n)
    (h : ∀ i, i ≠ j → σ i = τ i) : σ = τ := by
  apply Equiv.ext
  intro i
  by_cases hij : i = j
  · subst i
    obtain ⟨k,hk⟩ := τ.surjective (σ j)
    by_cases hkj : k = j
    · simpa only [hkj] using hk.symm
    · have hh := h k hkj
      have he : σ k = σ j := hh.trans hk
      exact False.elim (hkj (σ.injective he))
  · exact h i hij

lemma slaterTensor_orthonormal (φ : Fin n → α → ℂ)
    (hφ : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0)
    (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterTensor φ σ x) * slaterTensor φ τ x
      ∂Measure.pi (fun _ : Fin n => μ)) = if σ=τ then 1 else 0 := by
  rw [slaterTensor_inner]
  simp_rw [hφ]
  by_cases he : σ=τ
  · subst τ; simp
  · rw [ite_eq_right he]
    have hh : ∃ i, σ i ≠ τ i := by
      by_contra! hh
      exact he (Equiv.ext hh)
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma slaterRaw_norm_sq_integral {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0) :
    (∫ x, ‖slaterRaw φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) = n.factorial := by
  apply Complex.ofReal_injective
  change RCLike.ofReal (∫ x, ‖slaterRaw φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
    (RCLike.ofReal (n.factorial : ℝ) : ℂ)
  rw [← integral_ofReal (𝕜 := ℂ)]
  change (∫ x, (Complex.ofReal (‖slaterRaw φ x‖^2))
    ∂Measure.pi (fun _ : Fin n => μ)) = (n.factorial : ℂ)
  simp_rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  have hi (σ τ : Equiv.Perm (Fin n)) : Integrable (fun x =>
      conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
        (conj (slaterTensor φ σ x) * slaterTensor φ τ x))
      (Measure.pi fun _ : Fin n => μ) :=
    ((memLp_slaterTensor hφ σ).star.integrable_mul (memLp_slaterTensor hφ τ)).const_mul _
  have he (x : Fin n → α) : conj (slaterRaw φ x) * slaterRaw φ x =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
          (conj (slaterTensor φ σ x) * slaterTensor φ τ x) := by
    simp only [slaterRaw, map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hi σ τ))]
  simp_rw [integral_finsetSum _ (fun τ _ => hi _ τ), integral_const_mul,
    slaterTensor_orthonormal φ ho]
  have hs (σ : Equiv.Perm (Fin n)) :
      (∑ τ : Equiv.Perm (Fin n), conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
        (if σ=τ then 1 else 0)) = 1 := by
    rw [Finset.sum_eq_single σ]
    · simp only [ite_true, mul_one, map_intCast]
      exact (pow_two _).symm.trans (complex_sign_sq σ)
    · intro τ _ ht
      rw [ite_eq_right (Ne.symm ht), mul_zero]
    · simp
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin]

def slater (φ : Fin n → α → ℂ) (x : Fin n → α) : ℂ :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ * slaterRaw φ x

lemma memLp_slater {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ) :
    MemLp (slater φ) 2 (Measure.pi fun _ : Fin n => μ) :=
  (memLp_slaterRaw hφ).const_mul _

lemma slater_norm_sq_integral {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0) :
    (∫ x, ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) = 1 := by
  simp only [slater, norm_mul, mul_pow, integral_const_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity), slaterRaw_norm_sq_integral hφ ho]
  exact inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero)

end CoulombAtom

end

end OAI
