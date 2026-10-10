import OAI.Analysis.Pureness.Quasitrace.QuasitraceSqrtAddition
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNormBounds
import Mathlib.Tactic.Module

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma weighted_star_square (x y : D) (r : ℝ) (hr : r ≠ 0) :
    star (x+y)*(x+y)+star (r • x-r⁻¹ • y)*(r • x-r⁻¹ • y) =
      (1+r*r) • (star x*x)+(1+r⁻¹*r⁻¹) • (star y*y) := by
  simp only [star_add,star_sub,star_smul,star_trivial,add_mul,mul_add,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm]
  match_scalars <;> field_simp <;> ring

lemma star_square_add_le_weighted (x y : D) (r : ℝ) (hr : r ≠ 0) :
    star (x+y)*(x+y) ≤ (1+r*r) • (star x*x)+(1+r⁻¹*r⁻¹) • (star y*y) := by
  rw [← weighted_star_square x y r hr]
  exact le_add_of_nonneg_right (star_mul_self_nonneg _)

theorem finiteSpectralPositiveQuasitrace_square_add_weighted
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (x y : FinMatrix A n) (r : ℝ) (hr : r ≠ 0) :
    let T := finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
    T (Positive.starMul (x+y)) ≤
      (Real.sqrt ((1+r*r)*T (Positive.starMul x))+
        Real.sqrt ((1+r⁻¹*r⁻¹)*T (Positive.starMul y)))^2 := by
  let T := finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
  let u : ℝ≥0 := ⟨1+r*r,by nlinarith [sq_nonneg r]⟩
  let v : ℝ≥0 := ⟨1+r⁻¹*r⁻¹,by nlinarith [sq_nonneg r⁻¹]⟩
  have ho : Positive.starMul (x+y) ≤ Positive.add
      (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y)) :=
    star_square_add_le_weighted x y r hr
  have hs := finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite n
    (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y))
  change Real.sqrt (T _) ≤ Real.sqrt (T _)+Real.sqrt (T _) at hs
  rw [T.map_smul,T.map_smul] at hs
  exact (T.monotone ho).trans (by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hs
    rwa [Real.sq_sqrt (T.nonneg _)] at hsq)
end CuntzPureness

end

end OAI
