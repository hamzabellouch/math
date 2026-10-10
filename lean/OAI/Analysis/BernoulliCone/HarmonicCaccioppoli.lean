import OAI.Analysis.BernoulliCone.HarmonicReplacement

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
namespace HarmonicReplacement
variable {d : ℕ} {D : Set (Space d)}

/-- Caccioppoli's inequality for the genuine weak harmonic replacement.
The only test inserted is a proved H¹₀ product; no smoothness of u is used. -/
lemma caccioppoli {u : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hu : H1 D u G)
    (ho : ∀ v V, H10 D v V → (∫ x in D, inner ℝ (G x) (V x)) = 0)
    {η : Space d → ℝ} (hη : Test D η) :
    (∫ x in D, ‖η x • G x‖^2) ≤ 4 * (∫ x in D, ‖u x • gradient η x‖^2) := by
  let A : Space d → Space d := fun x => η x • G x
  let B : Space d → Space d := fun x => u x • gradient η x
  let V : Space d → Space d := fun x =>
    (η x * η x) • G x + u x • gradient (fun y => η y * η y) x
  have hA : MemLp A 2 (volume.restrict D) := hη.memLp_top.smul hu.2.1
  have hB : MemLp B 2 (volume.restrict D) := hu.1.smul hη.memLp_gradient_top
  have ht := SobolevDensity.h10_mul_test hu hD (hη.mul hη)
  have hv : MemLp V 2 (volume.restrict D) := ht.1.2.1
  have hz : (∫ x in D, inner ℝ (G x) (V x)) = 0 := ho _ _ ht
  have hi : Integrable (fun x => inner ℝ (G x) (V x)) (volume.restrict D) :=
    integrable_inner_of_memLp hu.2.1 hv
  have hA2 := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hB2 := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hp (x : Space d) : ‖A x‖^2 ≤
      2 * inner ℝ (G x) (V x) + 4 * ‖B x‖^2 := by
    have he : inner ℝ (G x) (V x) = ‖A x‖^2 + 2 * inner ℝ (A x) (B x) := by
      dsimp only [A,B,V]
      rw [hη.gradient_mul hη]
      simp only [inner_add_right,real_inner_smul_right,smul_add,
        real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
        real_inner_self_eq_norm_sq]
      ring
    have hs := norm_add_sq_real (A x) ((2:ℝ) • B x)
    simp only [inner_smul_right,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hs
    rw [he]
    nlinarith only [hs,sq_nonneg ‖A x + (2:ℝ) • B x‖]
  have hh := integral_mono_ae hA2 ((hi.const_mul 2).add (hB2.const_mul 4))
    (ae_of_all _ hp)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi.const_mul 2) (hB2.const_mul 4),integral_const_mul,
    integral_const_mul,hz,mul_zero,zero_add] at hh
  exact hh

end HarmonicReplacement
end Bernoulli

end
end

end OAI
