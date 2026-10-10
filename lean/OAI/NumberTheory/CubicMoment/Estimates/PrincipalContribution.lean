import OAI.NumberTheory.CubicMoment.Estimates.CubeLatticeBounds
import OAI.NumberTheory.CubicMoment.Estimates.CubePoisson

namespace OAI

/-!
# The absolute principal contribution to short dispersion

The actual cube-frequency kernel includes the Poisson scalar and the
three-to-one multiplicity. Its bound has size `A^(2/3) N(ab)^(-1/6)`.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma principal_cube_prefactor_scale {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    (A/(27*Real.sqrt R))/(A/(27*R))^(1/3:ℝ) =
      (1/9:ℝ)*A^(2/3:ℝ)*R^(-(1/6:ℝ)) := by
  have h27 : (27:ℝ)^(1/3:ℝ) = 3 := by
    rw [show (27:ℝ) = 3^3 by norm_num,← Real.rpow_natCast (3:ℝ) 3,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hAA : A/A^(1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one A]
    rw [← Real.rpow_sub hA]
    norm_num
  have hRR : R^(1/3:ℝ)/R^(1/2:ℝ) = R^(-(1/6:ℝ)) := by
    rw [← Real.rpow_sub hR]
    norm_num
  rw [Real.div_rpow hA.le (by positivity : 0 ≤ 27*R),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) hR.le,h27,Real.sqrt_eq_rpow]
  calc
    _ = (1/9:ℝ)*(A/A^(1/3:ℝ))*(R^(1/3:ℝ)/R^(1/2:ℝ)) := by field_simp; ring
    _ = _ := by rw [hAA,hRR]

/-- The principal kernel after its exact three-to-one cube reindexing. -/
def principalCubeKernel (a b : Eisenstein) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ((A/(27*Real.sqrt (norm (b*a))) : ℝ) : ℂ) *
    ∑' j : Eisenstein, if j = 0 then 0 else
      (if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0)

/-- Uniform over the arithmetic coprimality restrictions in the cube
kernel; no roughness or coefficient cancellation is used here. -/
theorem principalCubeKernel_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → ∀ a b : Eisenstein,
      a ≠ 0 → b ≠ 0 →
      ‖principalCubeKernel a b W A‖ ≤ C*A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_weighted_bound W hW hW'
  refine ⟨K/9,by positivity,?_⟩
  intro A hA a b ha hb
  have hR : 0 < norm (b*a) := norm_pos_of_ne_zero (mul_ne_zero hb ha)
  let c := A/(27*norm (b*a))
  let q := c^(1/3:ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hq : 0 < q := Real.rpow_pos_of_pos hc _
  have hq3 : q^3 = c := by
    dsimp [q]
    rw [← Real.rpow_natCast,← Real.rpow_mul hc.le]
    norm_num
  let w (j : Eisenstein) : ℂ := if IsCoprime a j ∧ IsCoprime b j then 1 else 0
  have hw : ∀ j, ‖w j‖ ≤ 1 := by intro j; dsimp only [w]; split_ifs <;> simp
  have hv := hbound q hq w hw
  have he : (∑' j : Eisenstein, if j = 0 then (0:ℂ) else
      w j*radialDualProfile W (q^3*(norm j)^3)) =
      ∑' j : Eisenstein, if j = 0 then 0 else
        (if IsCoprime a j ∧ IsCoprime b j then
          radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0) := by
    apply tsum_congr
    intro j
    rw [hq3]
    have ht : c*(norm j)^3 = A*(norm j)^3/(27*norm (b*a)) := by dsimp [c]; ring
    rw [ht]
    by_cases hj : j = 0 <;> by_cases hcop : IsCoprime a j ∧ IsCoprime b j <;> simp [hj,hcop,w]
  rw [he] at hv
  unfold principalCubeKernel
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq
  calc
    _ = K*((A/(27*Real.sqrt (norm (b*a))))/q) := by ring
    _ = _ := by dsimp [q,c]; rw [principal_cube_prefactor_scale hA hR]; ring

def principalBilinearContribution (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ B, ∑ b ∈ B,
    (β a*normTwist u a)*star (β b*normTwist u b)*principalCubeKernel a b W A

/-- The actual principal bilinear contribution satisfies the `l¹` term
of the short-dispersion estimate, uniformly in the height. -/
theorem principalBilinearContribution_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B₀ : ℝ, 0 < A → 0 < B₀ →
      ∀ B : Finset Eisenstein, (∀ b ∈ B, B₀ ≤ norm b) →
      ∀ β : Eisenstein → ℂ, ∀ u : ℝ,
      ‖principalBilinearContribution B β u W A‖ ≤
        C*A^(2/3:ℝ)*B₀^(-(1/3:ℝ))*(∑ b ∈ B, ‖β b‖)^2 := by
  obtain ⟨C,hC,hbound⟩ := principalCubeKernel_bound W hW hW'
  refine ⟨C,hC,?_⟩
  intro A B₀ hA hB₀ B hB β u
  let M := C*A^(2/3:ℝ)*B₀^(-(1/3:ℝ))
  have hpoint (a : Eisenstein) (ha : a ∈ B) (b : Eisenstein) (hb : b ∈ B) :
      ‖principalCubeKernel a b W A‖ ≤ M := by
    have han : 0 < norm a := hB₀.trans_le (hB a ha)
    have hbn : 0 < norm b := hB₀.trans_le (hB b hb)
    apply (hbound A hA a b (norm_eq_zero_iff.not.mp han.ne') (norm_eq_zero_iff.not.mp hbn.ne')).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hN : B₀^2 ≤ norm (b*a) := by
      rw [norm_mul_eq,pow_two]
      exact mul_le_mul (hB b hb) (hB a ha) hB₀.le hbn.le
    have hr := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hB₀) hN
      (show -(1/6:ℝ) ≤ 0 by norm_num)
    have he : (B₀^2)^(-(1/6:ℝ)) = B₀^(-(1/3:ℝ)) := by
      rw [← Real.rpow_natCast B₀ 2,← Real.rpow_mul hB₀.le]
      norm_num
    exact hr.trans_eq he
  unfold principalBilinearContribution
  calc
    _ ≤ ∑ a ∈ B, ∑ b ∈ B,
        ‖(β a*normTwist u a)*star (β b*normTwist u b)*principalCubeKernel a b W A‖ := by
      apply (norm_sum_le B _).trans
      exact Finset.sum_le_sum (fun a ha => norm_sum_le B _)
    _ ≤ ∑ a ∈ B, ∑ b ∈ B, ‖β a‖*‖β b‖*M := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      simp only [norm_mul,norm_star,norm_normTwist,mul_one]
      exact mul_le_mul_of_nonneg_left (hpoint a ha b hb) (by positivity)
    _ = M*(∑ b ∈ B, ‖β b‖)^2 := by
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := rfl

end CubicFirstMoment

end

end OAI
