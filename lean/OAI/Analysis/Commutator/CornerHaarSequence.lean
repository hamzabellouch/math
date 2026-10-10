import Mathlib
import OAI.Analysis.Commutator.CornerAlgebra
import OAI.Analysis.Commutator.HaarSequence

namespace OAI

noncomputable section

noncomputable section

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

end Kadison

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder

end Kadison

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace Filter Topology

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : τ 1=1) (z : unitary A)

end Kadison

namespace Kadison

open scoped InnerProductSpace ComplexOrder

open UniformSpace Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : A} (hp : IsStarProjection p) (τ : A →ₚ[ℂ] ℂ)

variable {r : ℝ} (hr : 0<r) (hτp : τ p=(r : ℂ))

def cornerScaled (r : ℝ) (a : Corner hp) : A :=
  ((Real.sqrt r)⁻¹ : ℂ) • (a : A)

lemma cornerScaled_gram (a b : Corner hp) :
    τ (star (cornerScaled hp r a)*cornerScaled hp r b)=
      cornerFunctional hp τ r hr (star a*b) := by
  have hc : star ((Real.sqrt r)⁻¹ : ℂ)*((Real.sqrt r)⁻¹ : ℂ)=(r⁻¹ : ℝ) := by
    rw [show ((Real.sqrt r)⁻¹ : ℂ) = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) by simp,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_inv_rev, ← pow_two, Real.sq_sqrt hr.le]
  unfold cornerScaled
  rw [star_smul, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_smul, hc]
  simp only [cornerFunctional_apply, corner_mul, corner_star, Complex.real_smul,
    smul_eq_mul]

include hτp in
lemma cornerHaar_orthonormal (z : unitary (Corner hp))
    (hH : ∀ n : ℕ, 0<n → cornerFunctional hp τ r hr ((z : Corner hp)^n)=0) :
    Orthonormal ℂ (fun n : ℕ =>
      (τ.toPreGNS (cornerScaled hp r ((z : Corner hp)^n)) : τ.GNS)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  change τ (star (cornerScaled hp r ((z : Corner hp)^n))*
    cornerScaled hp r ((z : Corner hp)^m))=_
  rw [cornerScaled_gram]
  exact haar_pow_gram _ (cornerFunctional_normalized hp τ hr hτp) z hH n m

end Kadison

namespace Kadison

open scoped InnerProductSpace ComplexOrder

open UniformSpace Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : A} (hp : IsStarProjection p) (τ : A →ₚ[ℂ] ℂ)

variable {r : ℝ} (hr : 0<r) (hτp : τ p=(r : ℂ))

omit [PartialOrder A] [StarOrderedRing A] in
lemma cornerScaled_star (a : Corner hp) :
    cornerScaled hp r (star a) = star (cornerScaled hp r a) := by
  simp only [cornerScaled, star_smul, corner_star]
  congr 1
  simp

include hr in
omit [PartialOrder A] [StarOrderedRing A] in
lemma cornerScaled_star_mul_self (z : unitary (Corner hp)) :
    star (cornerScaled hp r (z : Corner hp))*cornerScaled hp r (z : Corner hp) =
      (r⁻¹ : ℝ) • p := by
  have hc : star ((Real.sqrt r)⁻¹ : ℂ)*((Real.sqrt r)⁻¹ : ℂ)=(r⁻¹ : ℝ) := by
    rw [show ((Real.sqrt r)⁻¹ : ℂ) = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) by simp,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_inv_rev, ← pow_two, Real.sq_sqrt hr.le]
  simp only [cornerScaled, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm, hc]
  have hz : star (z : Corner hp)*(z : Corner hp)=1 := Unitary.coe_star_mul_self z
  have hz' := congrArg (fun a : Corner hp => (a : A)) hz
  simp only [corner_mul, corner_star, corner_one] at hz'
  rw [hz']
  exact Complex.coe_smul _ _

include hτp in
lemma cornerHaar_norm_one (z : unitary (Corner hp)) (n : ℕ)
    (hH : ∀ k : ℕ, 0<k → cornerFunctional hp τ r hr ((z : Corner hp)^k)=0) :
    ‖τ.toPreGNS (cornerScaled hp r ((z : Corner hp)^n))‖=1 := by
  have h := (cornerHaar_orthonormal hp τ hr hτp z hH).norm_eq_one n
  simpa only [Completion.norm_coe] using h

lemma cornerHaar_centered (z : unitary (Corner hp)) {n : ℕ} (hn : 0<n)
    (hH : ∀ k : ℕ, 0<k → cornerFunctional hp τ r hr ((z : Corner hp)^k)=0) :
    τ (cornerScaled hp r ((z : Corner hp)^n))=0 := by
  have hz : τ (((z : Corner hp)^n : Corner hp) : A)=0 := by
    have hh := hH n hn
    simpa only [cornerFunctional_apply, smul_eq_zero, inv_eq_zero, hr.ne', false_or] using hh
  simp only [cornerScaled, map_smul, hz, smul_zero]

include hτp in
lemma cornerHaar_moments_tendsto_zero (z : unitary (Corner hp))
    (hH : ∀ n : ℕ, 0<n → cornerFunctional hp τ r hr ((z : Corner hp)^n)=0) (a : A) :
    Tendsto (fun n => τ (cornerScaled hp r ((z : Corner hp)^n)*a)) atTop (𝓝 0) := by
  have hon := cornerHaar_orthonormal hp τ hr hτp z⁻¹ (inverse_haar_moments _ z hH)
  have h := orthonormal_inner_tendsto_zero _ hon (τ.toPreGNS a : τ.GNS)
  have hs (n : ℕ) : star (cornerScaled hp r (((z⁻¹ : unitary (Corner hp)) : Corner hp)^n)) =
      cornerScaled hp r ((z : Corner hp)^n) := by
    rw [←cornerScaled_star, star_pow]
    congr 2
    exact star_star (z : Corner hp)
  simpa only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, hs] using h

end Kadison
end
end
end

end OAI
