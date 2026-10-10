import Mathlib
import OAI.Probability.LogConcave.Numerics.MeanTree

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped NNReal

theorem primitiveExpectedField_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) {r : ℝ} (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/4) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ),by positivity⟩ (fun x => primitiveExpectedField F x r) := by
  let a := Real.sqrt 2
  have ha : 0<a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a^2=2 := Real.sq_sqrt (by norm_num)
  have hhalf : 0≤1/a := by positivity
  have hhalf1 : 1/a<1 := by rw [div_lt_iff₀ ha]; nlinarith
  have hvar : 1-(1/a)^2=1/2 := by field_simp; nlinarith
  have hsqrt : Real.sqrt (1-(1/a)^2)=1/a := by
    have hs := Real.sq_sqrt (show 0≤1-(1/a)^2 by rw [hvar]; norm_num)
    nlinarith [Real.sqrt_nonneg (1-(1/a)^2)]
  have hscale : (a*r)*Real.sqrt (1-(1/a)^2)=r := by rw [hsqrt]; field_simp
  have hmean (x : Point d) :
      conditionalFieldMean F 0 (a*r) (1/a) ((1/r) • x)=primitiveExpectedField F x r := by
    rw [MeanTree.conditionalFieldMean_primitive hF _ _ _ _ (by rw [hvar]; norm_num),hscale]
    congr 1
    simp only [zero_add,smul_smul]
    have he : a*r*(1/a)*(1/r)=1 := by field_simp
    rw [he,one_smul]
  have hL := conditionalFieldMean_lipschitz hF (0:Point d) (r:=a*r) (ρ:=1/a)
    (by positivity) (by rw [mul_pow,ha2]; nlinarith) hhalf hhalf1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [←hmean x,←hmean y]
  have hh := hL.dist_le_mul ((1/r) • x) ((1/r) • y)
  rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (by positivity : 0<1/r)] at hh
  apply hh.trans_eq
  change (Real.pi^2/2)*(1/a)*((lam:ℝ)*(a*r))*((1/r)*dist x y)=
    ((Real.pi^2/2)*(lam:ℝ))*dist x y
  field_simp
end LogConcaveSampling

end

end

end OAI
