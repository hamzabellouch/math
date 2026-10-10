import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealStableCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Real independent physical vectors stay independent in the doubled space -/

namespace DefocusingNLS

section
variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
local notation "H" => HomogeneousY a k
local notation "ι" => homogeneousComplexEmbed a k ha ha1 hk
local notation "X" => homogeneousComplexReal a k ha ha1 hk
local notation "Y" => homogeneousComplexImag a k ha ha1 hk

theorem homogeneousComplexReal_smul_embed (c : ℂ) (u : H) :
    X (c • ι u) = c.re • u := by
  have he : c • ι u = c.re • ι u + c.im • (Complex.I • ι u) := by
    conv_lhs => rw [← c.re_add_im]
    simp only [add_smul, mul_smul, Complex.coe_smul]
    rfl
  rw [he, map_add, map_smul, map_smul, homogeneousComplexReal_I,
    homogeneousComplexReal_embed, homogeneousComplexImag_embed, neg_zero, smul_zero, add_zero]

theorem homogeneousComplexImag_smul_embed (c : ℂ) (u : H) :
    Y (c • ι u) = c.im • u := by
  have he : c • ι u = c.re • ι u + c.im • (Complex.I • ι u) := by
    conv_lhs => rw [← c.re_add_im]
    simp only [add_smul, mul_smul, Complex.coe_smul]
    rfl
  rw [he, map_add, map_smul, map_smul, homogeneousComplexImag_I,
    homogeneousComplexReal_embed, homogeneousComplexImag_embed, smul_zero, zero_add]

theorem homogeneousComplexEmbed_linearIndependent {J : Type*} [Fintype J]
    (v : J → H) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun j => ι (v j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hr := congrArg X hc
  have hi := congrArg Y hc
  simp only [map_sum, homogeneousComplexReal_smul_embed, map_zero] at hr
  simp only [map_sum, homogeneousComplexImag_smul_embed, map_zero] at hi
  exact Complex.ext (Fintype.linearIndependent_iff.mp hv (fun j => (c j).re) hr j)
    (Fintype.linearIndependent_iff.mp hv (fun j => (c j).im) hi j)

end
end DefocusingNLS

end OAI
