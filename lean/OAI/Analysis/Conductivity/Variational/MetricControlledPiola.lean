import Mathlib
import OAI.Analysis.Conductivity.Flux.LocalTensorBounds
import OAI.Analysis.Conductivity.Sources.PhysicalC1Pullback

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma localPiolaTensor_bound_of_coefficient
    (X : OpenPartialHomeomorph Coord3 Coord3) {K : Set Coord3} {C : ℝ} (hC : 0≤C)
    (hc : ∀ x∈K,9*|(fderiv ℝ X x).det|⁻¹*‖operatorMatrix (fderiv ℝ X x)‖*
      ‖operatorMatrix (fderiv ℝ X x)‖≤C)
    (B : Coord3 → Mat3) (hB : Function.support B⊆K) (y : Coord3) :
    ‖localPiolaTensor X B y‖≤C*‖B (X.symm y)‖ := by
  let A := fun x => operatorMatrix (fderiv ℝ X x)
  by_cases hy : y∈X.target
  · by_cases hxy : X.symm y∈K
    · simp only [localPiolaTensor,ite_eq_left hy,norm_smul,Real.norm_eq_abs,abs_inv,abs_abs]
      calc
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*‖A (X.symm y)*B (X.symm y)‖*‖(A (X.symm y))ᵀ‖) :=
          mul_le_mul_of_nonneg_left (matrix_three_product_norm_bound _ _) (inv_nonneg.mpr (abs_nonneg _))
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*(3*‖A (X.symm y)‖*‖B (X.symm y)‖)*‖A (X.symm y)‖) := by
          rw [Matrix.norm_transpose]
          gcongr
          exact matrix_three_product_norm_bound _ _
        _ = (9*|(fderiv ℝ X (X.symm y)).det|⁻¹*‖A (X.symm y)‖*‖A (X.symm y)‖)*‖B (X.symm y)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hc _ hxy) (norm_nonneg _)
    · have hz : B (X.symm y)=0 := by
        by_contra hn
        exact hxy (hB hn)
      simp [localPiolaTensor,hy,hz]
  · simp only [localPiolaTensor,ite_eq_right hy,norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

theorem localPiolaSource_inverse_C1_of_bounds
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {K : Set Coord3} (hKs : K⊆X.source) {B : ℝ} (hB : 0<B)
    (hwb : ∀ x∈K,|inverseSourceWeight X x|≤B ∧ ‖fderiv ℝ (inverseSourceWeight X) x‖≤B)
    (hDX : ∀ x∈K,‖fderiv ℝ X x‖≤B)
    (r : Coord3 → ℝ) (hr : ContDiff ℝ (↑(⊤:ℕ∞)) r)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X '' K)
    (M : ℝ) (hM : 0≤M) (hb : UniformC1Bound r M) :
    UniformC1Bound (localPiolaSource X.symm r) (B*(B+1)*M) := by
  let w := inverseSourceWeight X
  have hw := inverseSourceWeight_smooth X hX hXi
  let p := localPiolaSource X.symm r
  have hps : tsupport p⊆K := localPiolaSource_inverse_support X r hc hKs hs
  intro x
  change |p x|≤B*(B+1)*M ∧ ‖fderiv ℝ p x‖≤B*(B+1)*M
  by_cases hx : x∈K
  · have hxs := hX.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have hws := hw.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have he : p=ᶠ[𝓝 x] (fun y => w y*r (X y)) := by
      filter_upwards [X.open_source.mem_nhds (hKs hx)] with y hy
      simp [p,localPiolaSource,hy,w,inverseSourceWeight]
    have hrc : DifferentiableAt ℝ (fun y => r (X y)) x :=
      (hr.differentiable (by simp) (X x)).comp x (hxs.differentiableAt (by simp))
    refine ⟨?_,?_⟩
    · rw [he.eq_of_nhds,abs_mul]
      exact (mul_le_mul (hwb x hx).1 (hb (X x)).1 (abs_nonneg _) hB.le).trans
        (by nlinarith [mul_nonneg hB.le hM,sq_nonneg B])
    · rw [he.fderiv_eq,fderiv_fun_mul (hws.differentiableAt (by simp)) hrc]
      have hchain := ((hr.differentiable (by simp) (X x)).hasFDerivAt.comp x
        (hxs.differentiableAt (by simp)).hasFDerivAt).fderiv
      have hcomp : ‖fderiv ℝ (fun y => r (X y)) x‖≤M*B := by
        change ‖fderiv ℝ (r ∘ X) x‖≤_
        rw [hchain]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hb (X x)).2 (hDX x hx) (norm_nonneg _) hM)
      calc
        _ ≤ ‖w x • fderiv ℝ (fun y => r (X y)) x‖+‖r (X x) • fderiv ℝ w x‖ := norm_add_le _ _
        _ = |w x| *‖fderiv ℝ (fun y => r (X y)) x‖+|r (X x)| *‖fderiv ℝ w x‖ := by
          simp only [norm_smul,Real.norm_eq_abs]
        _ ≤ B*(M*B)+M*B := add_le_add
          (mul_le_mul (hwb x hx).1 hcomp (norm_nonneg _) hB.le)
          (mul_le_mul (hb (X x)).1 (hwb x hx).2 (norm_nonneg _) hM)
        _ = _ := by ring
  · have hn : x∉tsupport p := fun h => hx (hps h)
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn,abs_zero,norm_zero]
    exact ⟨by positivity,by positivity⟩

end ScalarConductivity

end
end

end OAI
