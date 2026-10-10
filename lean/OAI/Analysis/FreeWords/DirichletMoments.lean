import Mathlib
import OAI.Analysis.FreeWords.ConjugateFree
import OAI.Analysis.FreeWords.DirichletCounts

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def dirichletRow (u : unitary A) (N : ℕ) : A :=
  (Real.sqrt (N : ℝ))⁻¹ • ∑ r ∈ Finset.range N, upow u (r+1)

def regularizedScalar (τ : A →ₚ[ℂ] ℂ) (n : ℕ) (p f : A) : ℝ :=
  let a := p * f^2 * p
  (n : ℝ) * (τ (a * star a *
    cfc (fun t : ℝ => (Real.sqrt (t + 1/100))⁻¹) (a * star a))).re

end

end KKFreeWords

namespace KKFreeWords

open scoped BigOperators

noncomputable section

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

omit [StarOrderedRing A] in
theorem positiveMap_real_smul (r : ℝ) (x : A) : τ (r • x) = r • τ x :=
  τ.toLinearMap.map_smul_of_tower r x

theorem haar_upow_orthonormal (hτ : FaithfulTracial τ) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) :
    Orthonormal ℂ (fun k : ℕ => τ.toPreGNS (upow u (k+2))) := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,
    star_upow,← upow_add]
  split_ifs with h
  · subst l; simp [hτ.1]
  · exact hHaar _ (by omega)

theorem haar_dirichlet_coefficient (hτ : FaithfulTracial τ) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) (N k : ℕ) :
    inner ℂ (τ.toPreGNS (upow u (k+2)))
      (τ.toPreGNS ((∑ r ∈ Finset.range N, upow u (r+1))^2)) =
      (dirichletCount N k : ℂ) := by
  classical
  simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,
    star_upow,pow_two,Finset.sum_mul,Finset.mul_sum,map_sum,← upow_add]
  rw [dirichletCount, Finset.natCast_card_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp
  split_ifs with h
  · have he : -((k:ℤ)+2)+((j:ℤ)+1+((i:ℤ)+1)) = 0 := by omega
    rw [he,upow_zero,hτ.1]
  · exact hHaar _ (by omega)

theorem haar_dirichlet_energy (hτ : FaithfulTracial τ) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) {N : ℕ} (hN : 0 < N) :
    (2*(N:ℝ)^3+(N:ℝ))/3 ≤
      (τ (((∑ r ∈ Finset.range N, upow u (r+1))^2) *
        star ((∑ r ∈ Finset.range N, upow u (r+1))^2))).re := by
  have h := (haar_upow_orthonormal hτ u hHaar).sum_inner_products_le
    (s := Finset.range (2*N-1)) (τ.toPreGNS ((∑ r ∈ Finset.range N, upow u (r+1))^2))
  simp_rw [haar_dirichlet_coefficient hτ u hHaar,Complex.norm_natCast] at h
  rw [dirichletCount_energy hN,← inner_self_eq_norm_sq (𝕜 := ℂ),
    PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,hτ.2.1] at h
  exact h

omit [PartialOrder A] [StarOrderedRing A] in
theorem dirichletRow_square (u : unitary A) {N : ℕ} (hN : 0 < N) :
    (dirichletRow u N)^2 = (N:ℝ)⁻¹ • (∑ r ∈ Finset.range N, upow u (r+1))^2 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNr.le
  have hi : (Real.sqrt (N:ℝ))⁻¹*(Real.sqrt (N:ℝ))⁻¹ = (N:ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two,hs]
  simp only [dirichletRow,pow_two,smul_mul_assoc,mul_smul_comm,smul_smul,hi]

omit [StarOrderedRing A] in
theorem dirichletRow_square_centered (_ : FaithfulTracial τ) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) {N : ℕ} (hN : 0 < N) :
    τ ((dirichletRow u N)^2) = 0 := by
  rw [dirichletRow_square u hN]
  simp only [positiveMap_real_smul,pow_two,Finset.sum_mul,Finset.mul_sum,map_sum,← upow_add]
  have hz (i j : ℕ) : τ (upow u ((i:ℤ)+1+((j:ℤ)+1))) = 0 := hHaar _ (by omega)
  simp only [hz,Finset.sum_const_zero,smul_zero]

theorem dirichletRow_energy_lower (hτ : FaithfulTracial τ) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) {N : ℕ} (hN : 0 < N) :
    2*(N:ℝ)/3 ≤ (τ ((dirichletRow u N)^2*star ((dirichletRow u N)^2))).re := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have he := haar_dirichlet_energy hτ u hHaar hN
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg ((N:ℝ)⁻¹))
  rw [dirichletRow_square u hN]
  simp only [star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,positiveMap_real_smul,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hid : (N:ℝ)⁻¹ ^ 2 * ((2*(N:ℝ)^3+(N:ℝ))/3) =
      2*(N:ℝ)/3 + 1/(3*(N:ℝ)) := by
    field_simp
  rw [hid] at hm
  nlinarith [one_div_nonneg.mpr (by positivity : (0:ℝ) ≤ 3*(N:ℝ))]

end

end KKFreeWords
end

end OAI
