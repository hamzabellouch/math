import OAI.NumberTheory.Ostmann.QuadraticSieveGaussNorm

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve

def quadraticGaussUnit (q : ℕ) [NeZero q] : ℂ :=
  gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar / (Real.sqrt q : ℂ)

theorem quadraticGaussUnit_norm {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q) :
    ‖quadraticGaussUnit q‖ = 1 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have ht := quadratic_gauss_norm_sq hq hsq
  have hn : ‖gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar‖ = Real.sqrt q := by
    nlinarith [norm_nonneg (gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar), Real.sq_sqrt hqp.le]
  rw [quadraticGaussUnit, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, div_self hs.ne']

theorem poisson_scale_scalar {X q d : ℝ} (hX : 0 < X) (hq : 0 < q) (hd : 0 < d) :
    (X / (q * d)) * Real.sqrt d / Real.sqrt X =
      1 / Real.sqrt q / Real.sqrt ((q / X) * d) := by
  have hsX := Real.sqrt_pos.mpr hX
  have hsq := Real.sqrt_pos.mpr hq
  have hsd := Real.sqrt_pos.mpr hd
  rw [Real.sqrt_mul (div_nonneg hq.le hX.le), Real.sqrt_div hq.le]
  have eX := Real.sq_sqrt hX.le
  have eq := Real.sq_sqrt hq.le
  have ed := Real.sq_sqrt hd.le
  field_simp
  rw [eX, eq, ed]
  ring

end Ostmann.QuadraticCenter

end

end OAI
