import Mathlib
import OAI.Probability.SKBarriers.Scalar.TerminalPathStability

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathWeight_integral_abs_sub (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε) (x : ℝ) :
    (∫ z, |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x) ≤
      2*(Real.exp (2*ε)-1) := by
  have iF := hierarchyPathWeight_normalized n m f hf x
  have iG := hierarchyPathWeight_normalized n m g hg x
  calc
    _ ≤ ∫ z, (Real.exp (2*ε)-1)*(hierarchyPathWeight n m f z+hierarchyPathWeight n m g z)
        ∂fiberGaussian n x := integral_mono (iF.1.sub iG.1).abs
      ((iF.1.add iG.1).const_mul _) (hierarchyPathWeight_abs_sub_bound n m hm hmono hf hg hε hfg)
    _ = _ := by rw [integral_const_mul, integral_add iF.1 iG.1, iF.2, iG.2]; ring

theorem hierarchyPathLaw_observable_stability (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    {a b : ParameterSpace n → ℝ} (ha : Continuous a) (hb : Continuous b)
    {C δ : ℝ} (hC : 0 ≤ C) (haC : ∀ z, |a z| ≤ C) (hbC : ∀ z, |b z| ≤ C)
    (hab : ∀ z, |a z-b z| ≤ δ) (x : ℝ) :
    |(∫ z, a z ∂hierarchyPathLaw n m f x)-(∫ z, b z ∂hierarchyPathLaw n m g x)| ≤
      δ+2*C*(Real.exp (2*ε)-1) := by
  have iF := hierarchyPathWeight_normalized n m f hf x
  have iG := hierarchyPathWeight_normalized n m g hg x
  have ia := hierarchyPath_exp_integrable n m f hf x a ha
    (HasExpGrowth.of_bounded hC (fun z => by simpa only [Real.norm_eq_abs] using haC z))
  have ib := hierarchyPath_exp_integrable n m g hg x b hb
    (HasExpGrowth.of_bounded hC (fun z => by simpa only [Real.norm_eq_abs] using hbC z))
  have iD : Integrable (fun z => C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z|)
      (fiberGaussian n x) := (iF.1.sub iG.1).abs.const_mul C
  rw [hierarchyPathLaw_integral n m f hf, hierarchyPathLaw_integral n m g hg,
    ← integral_sub ia ib]
  have hpoint (z : ParameterSpace n) :
      |hierarchyPathWeight n m f z*a z-hierarchyPathWeight n m g z*b z| ≤
        hierarchyPathWeight n m f z*δ+C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| := by
    calc
      _ = |hierarchyPathWeight n m f z*(a z-b z)+
        (hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)*b z| := by congr 1; ring
      _ ≤ |hierarchyPathWeight n m f z*(a z-b z)|+
          |(hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)*b z| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul,abs_mul,abs_of_pos (hierarchyPathWeight_pos n m f z)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hab z) (hierarchyPathWeight_pos n m f z).le)
          (by
            simpa only [mul_comm C] using
              mul_le_mul_of_nonneg_left (hbC z)
                (abs_nonneg (hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)))
  calc
    _ ≤ ∫ z, |hierarchyPathWeight n m f z*a z-hierarchyPathWeight n m g z*b z| ∂fiberGaussian n x :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, hierarchyPathWeight n m f z*δ+
        C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x :=
      integral_mono (ia.sub ib).abs ((iF.1.mul_const δ).add ((iF.1.sub iG.1).abs.const_mul C)) hpoint
    _ = δ+C*(∫ z, |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x) := by
      rw [integral_add (iF.1.mul_const δ) iD,
        integral_mul_const, integral_const_mul, iF.2, one_mul]
    _ ≤ _ := by
      have H := mul_le_mul_of_nonneg_left (hierarchyPathWeight_integral_abs_sub n m hm hmono hf hg hε hfg x) hC
      nlinarith

end SK.Analytic

end
end

end OAI
