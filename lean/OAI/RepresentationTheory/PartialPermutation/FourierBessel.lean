import Mathlib
import OAI.RepresentationTheory.PartialPermutation.MatrixCoefficients
import OAI.RepresentationTheory.PartialPermutation.HilbertSchmidt

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
open scoped BigOperators ComplexConjugate MonoidAlgebra

noncomputable section

lemma fourier_bessel {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) [Representation.IsIrreducible ρ]
    (f : G → ℂ) :
    (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ f) ≤
      (Fintype.card G : ℝ) * ∑ g, ‖f g‖ ^ 2 := by
  classical
  let e := stdOrthonormalBasis ℂ V
  let t := Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G)
  let v := fun p : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V) =>
    (t : ℂ) • WithLp.toLp 2 (fun g : G => conj (inner ℂ (e p.1) (ρ g (e p.2))))
  have hv : Orthonormal ℂ v := normalized_matrixCoefficients_orthonormal ρ hρ e
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have ht : t ^ 2 = (Module.finrank ℂ V : ℝ) / Fintype.card G :=
    Real.sq_sqrt (by positivity)
  have inner_eq (p : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V)) :
      inner ℂ (v p) (WithLp.toLp 2 f) =
        (t : ℂ) * inner ℂ (e p.1) (complexFourier ρ f (e p.2)) := by
    simp [v, complexFourier, PiLp.inner_apply, RCLike.inner_apply, LinearMap.sum_apply]
  have h := hv.sum_inner_products_le (WithLp.toLp 2 f) (s := Finset.univ)
  simp only [PiLp.norm_sq_eq_of_L2] at h
  simp only [inner_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ t from Real.sqrt_nonneg _), mul_pow] at h
  rw [← Finset.mul_sum, ht, Fintype.sum_prod_type] at h
  have hs : ∑ i, ∑ j, ‖inner ℂ (e i) (complexFourier ρ f (e j))‖ ^ 2 =
      hsNormSq (complexFourier ρ f) := by
    rw [Finset.sum_comm, hsNormSq_eq_sum e]
    exact Finset.sum_congr rfl (fun j _ => e.sum_sq_norm_inner_right _)
  rw [hs] at h
  have h' := mul_le_mul_of_nonneg_left h hN.le
  calc
    _ = (Fintype.card G : ℝ) *
        ((Module.finrank ℂ V : ℝ) / Fintype.card G * hsNormSq (complexFourier ρ f)) := by
      field_simp
    _ ≤ _ := h'

end
end PartialPermutation

end

end OAI
