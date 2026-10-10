import Mathlib
import OAI.Analysis.FreeWords.CornerState
import OAI.Analysis.FreeWords.FreeCompressionMoments
import OAI.Analysis.FreeWords.RecoveryArithmetic
import OAI.Analysis.FreeWords.RegularizedOrder

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

end

end KKFreeWords

namespace KKFreeWords

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

theorem scalar_recovery_bound (hτ : FaithfulTracial τ)
    (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P))
    {p : A} (hp : p ∈ P) (hps : star p = p) (hpp : p*p = p)
    {n N : ℕ} (hn : 2 ≤ n) (htp : τ p = (n : ℂ)⁻¹)
    (hN : 100 * (n : ℝ) * (100 * Real.pi)^3 ≤ (N : ℝ)) :
    1/2 ≤ regularizedScalar τ n p (dirichletRow u N) := by
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hnz : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  have hpi : 1 ≤ (100*Real.pi)^3 := by
    calc 1 = (1:ℝ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ zero_le_one (by linarith [Real.pi_gt_three]) 3
  have hN100 : 100*(n:ℝ) ≤ (N:ℝ) := by
    have := mul_le_mul_of_nonneg_left hpi (by positivity : (0:ℝ) ≤ 100*(n:ℝ))
    linarith
  have hNr : (0:ℝ) < N := by linarith
  have hN0 : 0 < N := by exact_mod_cast hNr
  let a := (dirichletRow u N)^2
  let B := (p*a*p)*star (p*a*p)
  let σ := cornerState τ n p
  have ha : a ∈ S := by
    apply S.pow_mem
    change dirichletRow u N ∈ S
    unfold dirichletRow
    simpa only [Complex.coe_smul] using
      S.smul_mem (S.sum_mem (t := Finset.range N) (fun r hr => upow_mem u hu ((r:ℤ)+1)))
        (((Real.sqrt (N:ℝ))⁻¹ : ℝ) : ℂ)
  have hta : τ a = 0 := dirichletRow_square_centered hτ u hHaar hN0
  have hb : 0 ≤ B := mul_star_self_nonneg _
  have hpb : p*B = B := by
    dsimp [B]
    simp only [← mul_assoc,hpp]
  have hB2 := projection_compression_second hτ hfree (i := false) (j := true)
    (by decide) hp hps hpp ha hta
  have hB4 := projection_compression_fourth hτ hfree (i := false) (j := true)
    (by decide) hp hps hpp ha hta
  change τ B = (τ p)^2*τ (a*star a) at hB2
  change τ (B^2) = (τ p)^4*τ ((a*star a)^2) +
    2*(τ p)^3*(1-τ p)*(τ (a*star a))^2 at hB4
  have hsB : σ B = (n:ℂ)*τ B := cornerState_supported hτ n hps hpp hpb
  have hsB2 : σ (B^2) = (n:ℂ)*τ (B^2) := by
    simpa only [pow_two] using cornerState_leftMul_supported hτ n hps hpp hpb B
  have he2 : (n:ℂ)*σ B = τ (a*star a) := by
    rw [hsB,hB2,htp]
    field_simp
  have he4 : (n:ℂ)^3*σ (B^2) = τ ((a*star a)^2) +
      2*((n:ℂ)-1)*(τ (a*star a))^2 := by
    rw [hsB2,hB4,htp]
    field_simp
  have htareal : τ (a*star a) = ((τ (a*star a)).re : ℂ) := by
    have hz := (Complex.nonneg_iff.mp (τ.map_nonneg (mul_star_self_nonneg a))).2
    apply Complex.ext <;> simp [hz.symm]
  have he2r : (n:ℝ)*(σ B).re = (τ (a*star a)).re := by
    have := congrArg Complex.re he2
    simpa only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using this
  have he4r : (n:ℝ)^3*(σ (B^2)).re = (τ ((a*star a)^2)).re +
      2*((n:ℝ)-1)*(τ (a*star a)).re^2 := by
    rw [htareal] at he4
    have := congrArg Complex.re he4
    simpa only [← Complex.ofReal_natCast,← Complex.ofReal_pow,← Complex.ofReal_sub,
      ← Complex.ofReal_one,← Complex.ofReal_ofNat,← Complex.ofReal_mul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re] using this
  have hroot : (CFC.sqrt B)^2 = B := by
    simpa only [pow_two] using CFC.sqrt_mul_sqrt_self B hb
  have hroot4 : (CFC.sqrt B)^4 = B^2 := by
    rw [show 4 = 2*2 from rfl,pow_mul,hroot]
  have hinter := positiveMap_moment_interpolation (τ := σ) (CFC.sqrt_nonneg B)
  rw [hroot,hroot4] at hinter
  have hs : (3:ℝ)/5 ≤ (σ (CFC.sqrt B)).re := recovery_moment_arithmetic hnr hN100
    (dirichletRow_energy_lower hτ u hHaar hN0)
    (dirichletRow_fourth_upper hτ u hN0) he2r he4r
    (positiveMap_re_nonneg (CFC.sqrt_nonneg B)) hinter
  have hσ1 : σ 1 = 1 := cornerState_one hn0 hps hpp htp
  have hreg := regularized_state_lower hσ1 hb
  have hreg_eq : (σ (B*cfc (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) B)).re =
      regularizedScalar τ n p (dirichletRow u N) := by
    change (cornerState τ n p (B*cfc (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) B)).re = _
    rw [cornerState_leftMul_supported hτ n hps hpp hpb]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    rfl
  rw [hreg_eq] at hreg
  linarith

end

end KKFreeWords
end

end OAI
