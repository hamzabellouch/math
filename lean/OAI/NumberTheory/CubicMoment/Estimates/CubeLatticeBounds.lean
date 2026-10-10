import OAI.NumberTheory.CubicMoment.Estimates.CubeLattice
import OAI.NumberTheory.CubicGram.DyadicRecurrence

namespace OAI

/-!
# The correctly scaled absolute cube-lattice bound

The dyadic norm count and rapid decay give the norm-area scale `q⁻¹`
for a profile evaluated at `q³ N(j)³`. This is the cube contribution
needed even when no lattice asymptotic is available.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma cube_decay_comparison {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^2 ≤ 4*(1+x^3) := by
  have hs : x^2 ≤ 1+x^3 := by
    rcases le_total x 1 with h | h
    · have hsq : x^2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg hx 3]
    · have hp := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg x)
      nlinarith
  nlinarith [sq_nonneg (x-1),pow_nonneg hx 3]

lemma radial_cube_pointwise_bound (W : ℝ → ℂ) {C q : ℝ}
    (hq : 0 < q)
    (hbound : ∀ t : ℝ, 0 ≤ t → (1+t)*‖radialDualProfile W t‖ ≤ C)
    (a : Eisenstein) :
    ‖radialDualProfile W (q^3*(norm a)^3)‖ ≤ 4*C/(1+q*norm a)^2 := by
  have hn := norm_nonneg a
  have hp := cube_decay_comparison (mul_nonneg hq.le (norm_nonneg a))
  have hb := hbound (q^3*(norm a)^3) (by positivity)
  have he : (q*norm a)^3 = q^3*(norm a)^3 := mul_pow _ _ _
  rw [he] at hp
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1+q*norm a))).mpr
  have hmul := mul_le_mul_of_nonneg_right hp
    (_root_.norm_nonneg (radialDualProfile W (q^3*(norm a)^3)))
  nlinarith

/-- Uniform absolute bound at the cube-lattice scale. -/
theorem radial_cube_lattice_weighted_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ w : Eisenstein → ℂ,
      (∀ j, ‖w j‖ ≤ 1) →
      ‖∑' j : Eisenstein, if j = 0 then (0:ℂ) else
        w j*radialDualProfile W (q^3*(norm j)^3)‖ ≤ K/q := by
  obtain ⟨C,hC,hbound'⟩ := radialDualProfile_rapidDecay W hW hW' 1
  have hbound : ∀ t : ℝ, 0 ≤ t → (1+t)*‖radialDualProfile W t‖ ≤ C := by
    simpa only [pow_one] using hbound'
  refine ⟨288*C,by positivity,?_⟩
  intro q hq w hw
  let F (j : Eisenstein) : ℂ := if j = 0 then 0 else w j*radialDualProfile W (q^3*(norm j)^3)
  have hF : Summable F := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    by_cases hj : j = 0
    · simp only [F,ite_eq_left hj,norm_zero]
      exact _root_.norm_nonneg _
    · simp only [F,ite_eq_right hj,norm_mul]
      exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hw j)
  have hsum := hasSum_frequencyDyad F hF (by simp [F])
  have hrow (n : ℕ) : ‖∑ j ∈ frequencyDyad n, F j‖ ≤
      (144*C)*((2:ℝ)^n/(1+q*2^n)^2) := by
    have hden : 0 < (1+q*(2:ℝ)^n)^2 := by positivity
    calc
      _ ≤ ∑ j ∈ frequencyDyad n, ‖F j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ frequencyDyad n, 4*C/(1+q*(2:ℝ)^n)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        dsimp only [F]
        rw [ite_eq_right (mem_frequencyDyad.mp hj).1]
        rw [norm_mul]
        apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hw j)).trans
        apply (radial_cube_pointwise_bound W hq hbound j).trans
        apply div_le_div_of_nonneg_left (by positivity) hden
        exact pow_le_pow_left₀ (by positivity)
          (by nlinarith [(frequencyDyad_norm hj).1]) 2
      _ = (frequencyDyad n).card*(4*C/(1+q*(2:ℝ)^n)^2) := by simp
      _ ≤ (36*(2:ℝ)^n)*(4*C/(1+q*(2:ℝ)^n)^2) :=
        mul_le_mul_of_nonneg_right (frequencyDyad_card_le n) (by positivity)
      _ = _ := by ring
  change ‖∑' j : Eisenstein, F j‖ ≤ _
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, ‖∑ j ∈ frequencyDyad n, F j‖ := norm_tsum_le_tsum_norm hsum.summable.norm
    _ ≤ ∑' n : ℕ, (144*C)*((2:ℝ)^n/(1+q*2^n)^2) :=
      Summable.tsum_le_tsum hrow hsum.summable.norm ((dyadic_decay_summable hq).mul_left _)
    _ = (144*C)*(∑' n : ℕ, (2:ℝ)^n/(1+q*2^n)^2) := tsum_mul_left
    _ ≤ (144*C)*(2/q) := mul_le_mul_of_nonneg_left (dyadic_decay_tsum hq) (by positivity)
    _ = _ := by ring

/-- The unweighted cube lattice is a special case of the bound with
arbitrary fixed exclusions and unit-modulus twists. -/
theorem radial_cube_lattice_absolute_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q →
      ‖∑' j : Eisenstein, if j = 0 then (0:ℂ) else
        radialDualProfile W (q^3*(norm j)^3)‖ ≤ K/q := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_weighted_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq
  simpa only [one_mul] using hbound q hq (fun _ => 1) (by intro j; simp)

end CubicFirstMoment

end

end OAI
