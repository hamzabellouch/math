import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Jet Norm Equivalence. -/

section

 

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι]

def jetArray (e : ι → E) (m : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F →ₗ[ℝ]
      PiLp 2 (fun _ : Fin m → ι => F) where
  toFun T := WithLp.toLp 2 (fun σ => T (fun i => e (σ i)))
  map_add' T R := by ext σ; rfl
  map_smul' c T := by ext σ; rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [Fintype ι] in
lemma jetArray_injective (e : Basis ι ℝ E) (m : ℕ) :
    Function.Injective (jetArray (F := F) e m) := by
  intro T R h
  have he : T.toMultilinearMap = R.toMultilinearMap := Module.Basis.ext_multilinear (fun _ => e)
    (fun σ => congrArg (fun V : PiLp 2 (fun _ : Fin m → ι => F) => V σ) h)
  ext v
  exact congrArg (fun L => L v) he

omit [FiniteDimensional ℝ E] in
lemma jetArray_norm_control (e : Basis ι ℝ E) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F,
      ‖T‖ ≤ C*‖jetArray e m T‖ := by
  let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F) :=
    FiniteDimensional.of_injective (jetArray (F := F) e m) (jetArray_injective e m)
  obtain ⟨C,hC,hb⟩ := (jetArray (F := F) e m).injective_iff_antilipschitz.mp (jetArray_injective e m)
  refine ⟨C,by exact_mod_cast hC,fun T => ?_⟩
  simpa only [map_zero,dist_zero_right] using hb.le_mul_dist T 0

end HigherJet

end
end

end OAI
