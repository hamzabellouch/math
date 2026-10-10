import Mathlib
import OAI.Analysis.FreeWords.PositiveMoments

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

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} {τ : A →ₚ[ℂ] ℂ} {S : ι → StarSubalgebra ℂ A}

variable {i j : ι}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

def cornerState (τ : A →ₚ[ℂ] ℂ) (n : ℕ) (p : A) : A →ₚ[ℂ] ℂ where
  toFun x := (n:ℂ)*τ (star p*x*p)
  map_add' x y := by simp only [mul_add,add_mul,map_add,mul_add]
  map_smul' c x := by
    simp only [mul_smul_comm,smul_mul_assoc,map_smul,smul_eq_mul,RingHom.id_apply]
    ring
  monotone' x y h := by
    exact mul_le_mul_of_nonneg_left
      (τ.monotone' (star_left_conjugate_le_conjugate h p)) (by positivity)

@[simp] theorem cornerState_apply (n : ℕ) (p x : A) :
    cornerState τ n p x = (n:ℂ)*τ (star p*x*p) := rfl

theorem cornerState_one {n : ℕ} (hn : 0 < n) {p : A}
    (hps : star p = p) (hpp : p*p = p) (htp : τ p = (n:ℂ)⁻¹) :
    cornerState τ n p 1 = 1 := by
  have hnz : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [cornerState_apply,hps,mul_one,hpp,htp,mul_inv_cancel₀ hnz]

theorem cornerState_supported (hτ : FaithfulTracial τ) (n : ℕ) {p x : A}
    (hps : star p = p) (hpp : p*p = p) (hpx : p*x = x) :
    cornerState τ n p x = (n:ℂ)*τ x := by
  rw [cornerState_apply,hps,hτ.2.1 (p*x) p,← mul_assoc,hpp,hpx]

theorem cornerState_leftMul_supported (hτ : FaithfulTracial τ) (n : ℕ) {p b : A}
    (hps : star p = p) (hpp : p*p = p) (hpb : p*b = b) (x : A) :
    cornerState τ n p (b*x) = (n:ℂ)*τ (b*x) :=
  cornerState_supported hτ n hps hpp (by rw [← mul_assoc,hpb])

omit [StarOrderedRing A] in
theorem dirichletRow_square_norm (hτ : FaithfulTracial τ) (u : unitary A)
    {N : ℕ} (hN : 0 < N) : ‖(dirichletRow u N)^2‖ ≤ (N:ℝ) := by
  let : Nontrivial A := nontrivial_of_ne (0:A) 1 (by
    intro he
    have ht := congrArg τ he
    exact zero_ne_one (by simpa only [map_zero,hτ.1] using ht))
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hr : ‖∑ r ∈ Finset.range N, upow u (r+1)‖ ≤ (N:ℝ) := by
    calc _ ≤ ∑ r ∈ Finset.range N, ‖upow u (r+1)‖ := norm_sum_le _ _
      _ = _ := by simp [upow]
  have hp := (norm_pow_le (∑ r ∈ Finset.range N, upow u (r+1)) 2).trans
    (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  rw [dirichletRow_square u hN,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hNr.le)]
  calc _ ≤ (N:ℝ)⁻¹ * (N:ℝ)^2 := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hNr.le)
    _ = _ := by field_simp

theorem dirichletRow_fourth_upper (hτ : FaithfulTracial τ) (u : unitary A)
    {N : ℕ} (hN : 0 < N) :
    (τ (((dirichletRow u N)^2*star ((dirichletRow u N)^2))^2)).re ≤
      (N:ℝ)^2 * (τ ((dirichletRow u N)^2*star ((dirichletRow u N)^2))).re := by
  exact (positiveMap_fourth_le ((dirichletRow u N)^2)).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (dirichletRow_square_norm hτ u hN) 2)
      (positiveMap_re_nonneg (mul_star_self_nonneg _)))

end

end KKFreeWords
end

end OAI
