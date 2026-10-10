import OAI.Algebra.Finitistic.Tensor.BalancedProjectiveLeft
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalDifferential
import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorAcross

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The cross-variable tensor map with an identity input is the original bimodule map. -/
theorem tensorAcross_right_id {M M' : ModuleCat.{u} (Enveloping k B)}
    (f : M ⟶ M') (N : ModuleCat.{u} B) :
    tensorAcross f (𝟙 N) = BimoduleBalancedTensor.map k B (BalancedTensor.ScalarLeftModule k B N) f := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable (k B) (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable (hP : P.Acyclic) [∀ q, Projective (Z.X q)]

include hP in
/-- Every row of an acyclic bimodule complex tensored with a projective input term is exact. -/
theorem row_exact (a q : ℤ) :
    Function.Exact (tensorAcross (P.d (a-1) a) (𝟙 (Z.X q)))
      (tensorAcross (P.d a (a+1)) (𝟙 (Z.X q))) := by
  let : Module.Projective B (BalancedTensor.ScalarLeftModule k B (Z.X q)) :=
    inferInstanceAs (Module.Projective B (Z.X q))
  let S := ShortComplex.mk (P.d (a-1) a) (P.d a (a+1)) (P.d_comp_d (a-1) a (a+1))
  have hs : S.Exact :=
    (HomologicalComplex.exactAt_iff' P (a-1) a (a+1) (by simp) (by simp)).mp (hP a)
  have ht := BimoduleBalancedTensor.projectiveInput_mapsExact k B
    (BalancedTensor.ScalarLeftModule k B (Z.X q)) S hs
  rw [tensorAcross_right_id,tensorAcross_right_id]
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp ht

include hP in
/-- The row exactness statement with precisely the transports occurring in the signed total. -/
theorem horizontal_exact (n a : ℤ) :
    Function.Exact
      (horizontalBetween k B P Z (n-1) n (a-1) a (by omega) (by omega))
      (horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl) := by
  have ht := row_exact k B P Z hP a (n + -a)
  have transport (q₀ q₂ : ℤ) (h₀ : q₀ = n + -a) (h₂ : n + -a = q₂) :
      Function.Exact
        (tensorAcross (P.d (a-1) a) (eqToHom (congrArg Z.X h₀)))
        (tensorAcross (P.d a (a+1)) (eqToHom (congrArg Z.X h₂))) := by
    subst q₀ q₂
    exact ht
  unfold horizontalBetween
  rw [← tensorAcross_eq_termMap,← tensorAcross_eq_termMap]
  exact transport ((n-1) + -(a-1)) ((n+1) + -(a+1)) (by omega) (by omega)
end LittleFinitistic.BimoduleTotal

end

end OAI
