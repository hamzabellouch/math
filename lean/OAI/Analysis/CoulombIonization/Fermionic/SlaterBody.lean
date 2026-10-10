import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Slater

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

lemma complex_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℂ) :
    (∫ x, conj (f x) * f x ∂μ) = (∫ x, ‖f x‖^2 ∂μ : ℝ) := by
  calc
    _ = ∫ x, (Complex.ofReal (‖f x‖^2)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Complex.sq_norm] using
          (Complex.normSq_eq_conj_mul_self (z := f x)).symm)
    _ = _ := integral_ofReal (𝕜 := ℂ)

lemma integral_norm_sq_weighted_sum {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [Fintype ι] (a : ι → ℂ) (f : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) :
    (Complex.ofReal (∫ x, ‖∑ i, a i * f i x‖^2 ∂μ)) =
      ∑ i, ∑ j, conj (a i) * a j * (∫ x, conj (f i x) * f j x ∂μ) := by
  rw [← complex_integral_norm_sq]
  have hi (i j : ι) : Integrable (fun x => conj (a i) * a j *
      (conj (f i x) * f j x)) μ :=
    ((hf i).star.integrable_mul (hf j)).const_mul _
  have he (x : α) : conj (∑ i, a i * f i x) * (∑ i, a i * f i x) =
      ∑ i, ∑ j, conj (a i) * a j * (conj (f i x) * f j x) := by
    simp only [map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterCoordinateTensor (φ ψ : Fin n → α → ℂ) (j : Fin n)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) : ℂ :=
  ∏ i, (if i=j then ψ else φ) (σ i) (x i)

def slaterCoordinateRaw (φ ψ : Fin n → α → ℂ) (j : Fin n) (x : Fin n → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : ℂ) * slaterCoordinateTensor φ ψ j σ x

lemma memLp_slaterCoordinateTensor {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterCoordinateTensor φ ψ j σ) 2 (Measure.pi fun _ : Fin n => μ) := by
  have h (i : Fin n) : MemLp ((if i=j then ψ else φ) (σ i)) 2 μ := by
    split_ifs <;> first | exact hψ _ | exact hφ _
  have hm : AEStronglyMeasurable (slaterCoordinateTensor φ ψ j σ)
      (Measure.pi fun _ : Fin n => μ) := by
    unfold slaterCoordinateTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (h i).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterCoordinateTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : Fin n => (h i).norm.integrable_sq)

lemma memLp_slaterCoordinateRaw {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (j : Fin n) :
    MemLp (slaterCoordinateRaw φ ψ j) 2 (Measure.pi fun _ : Fin n => μ) :=
  memLp_finsetSum _ (fun σ _ => (memLp_slaterCoordinateTensor hφ hψ j σ).const_mul _)

lemma slaterCoordinateTensor_inner (φ ψ : Fin n → α → ℂ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (j : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterCoordinateTensor φ ψ j σ x) * slaterCoordinateTensor φ ψ j τ x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      if σ=τ then (∫ t, ‖ψ (σ j) t‖^2 ∂μ : ℝ) else 0 := by
  simp only [slaterCoordinateTensor, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i t => conj ((if i=j then ψ else φ) (σ i) t) *
      (if i=j then ψ else φ) (τ i) t)]
  by_cases he : σ=τ
  · subst τ
    rw [ite_eq_left rfl, Finset.prod_eq_single j]
    · simpa only [ite_eq_left (show j=j from rfl), ite_true] using
        complex_integral_norm_sq (μ := μ) (ψ (σ j))
    · intro i _ hij
      rw [ite_eq_right hij, ho, ite_eq_left rfl]
    · simp
  · rw [ite_eq_right he]
    have hh : ∃ i, i ≠ j ∧ σ i ≠ τ i := by
      by_contra! hh
      exact he (permutations_eq_of_agree_except σ τ j hh)
    obtain ⟨i,hij,hi⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hij, ho, ite_eq_right hi]

lemma slaterCoordinateRaw_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (j : Fin n) :
    (∫ x, ‖slaterCoordinateRaw φ ψ j x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ σ : Equiv.Perm (Fin n), ∫ t, ‖ψ (σ j) t‖^2 ∂μ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  change (Complex.ofReal (∫ x, ‖∑ σ : Equiv.Perm (Fin n),
    ((σ.sign : ℤ) : ℂ) * slaterCoordinateTensor φ ψ j σ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ))) = _
  rw [integral_norm_sq_weighted_sum _ _ (memLp_slaterCoordinateTensor hφ hψ j)]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [slaterCoordinateTensor_inner φ ψ ho]
  rw [Finset.sum_eq_single σ]
  · simp only [ite_true, map_intCast]
    rw [← pow_two, complex_sign_sq, one_mul]
  · intro τ _ ht
    simp only [ite_eq_right (Ne.symm ht), Complex.ofReal_zero, mul_zero]
  · simp

lemma slaterCoordinateRaw_sum_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0) :
    (∑ j : Fin n, ∫ x, ‖slaterCoordinateRaw φ ψ j x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      (n.factorial : ℝ) * ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ := by
  simp_rw [slaterCoordinateRaw_norm_sq_integral hφ hψ ho]
  rw [Finset.sum_comm]
  have he (σ : Equiv.Perm (Fin n)) :
      (∑ j, ∫ t, ‖ψ (σ j) t‖^2 ∂μ) = ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ :=
    Equiv.sum_comp σ (fun i => ∫ t, ‖ψ i t‖^2 ∂μ)
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end CoulombAtom

end

end OAI
