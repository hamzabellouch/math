import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelatedVectorFieldBracket
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace OAI

/-! # Differentiating a transported field along time

The bracket of the constant time field with a vertical field is its time
derivative. Naturality of brackets then identifies the derivative of a
field transported by a flow, without a separate mixed-partial computation.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_prod_apply_fst {f : ℝ × E → F} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (v : ℝ) :
    fderiv ℝ f p (v, 0) = fderiv ℝ (fun t => f (t, p.2)) p.1 v := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1)
  have hd := hf.hasFDerivAt.comp p.1 hi
  change HasFDerivAt (fun t => f (t, p.2)) _ p.1 at hd
  rw [hd.fderiv]
  rfl

theorem fderiv_prod_apply_snd {f : ℝ × E → F} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (v : E) :
    fderiv ℝ f p (0, v) = fderiv ℝ (fun z => f (p.1, z)) p.2 v := by
  have hi := (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) p.2)
  have hd := hf.hasFDerivAt.comp p.2 hi
  change HasFDerivAt (fun z => f (p.1, z)) _ p.2 at hd
  rw [hd.fderiv]
  rfl

theorem lieBracket_time_vertical {Z : ℝ × E → E} {p : ℝ × E}
    (hZ : DifferentiableAt ℝ Z p) :
    VectorField.lieBracket ℝ (fun _ : ℝ × E => ((1 : ℝ), (0 : E)))
      (fun q => ((0 : ℝ), Z q)) p = (0, fderiv ℝ Z p (1, 0)) := by
  have hd := (hasFDerivAt_const (0 : ℝ) p).prodMk hZ.hasFDerivAt
  have hc := (hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ), (0 : E)) p).fderiv
  rw [VectorField.lieBracket, hd.fderiv, hc]
  simp only [ContinuousLinearMap.prod_apply, zero_apply,
    sub_zero]

theorem lieBracket_suspended_vertical {X Y : E → E} {p : ℝ × E}
    (hX : DifferentiableAt ℝ X p.2) (hY : DifferentiableAt ℝ Y p.2) :
    VectorField.lieBracket ℝ (fun q : ℝ × E => ((1 : ℝ), X q.2))
      (fun q => ((0 : ℝ), Y q.2)) p = (0, VectorField.lieBracket ℝ X Y p.2) := by
  have hdX := (hasFDerivAt_const (1 : ℝ) p).prodMk
    (hX.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
  have hdY := (hasFDerivAt_const (0 : ℝ) p).prodMk
    (hY.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
  dsimp only [Function.comp_def] at hdX hdY
  rw [VectorField.lieBracket, hdY.fderiv, hdX.fderiv]
  simp only [ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.comp_apply,
    Prod.mk_sub_mk, sub_self, VectorField.lieBracket]
  rfl

theorem transportedField_time_derivative {F : ℝ × E → ℝ × E}
    {Z : ℝ × E → E} {X Y : E → E} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x))
    (hZ : DifferentiableAt ℝ Z (0, x))
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hbase : F (0, x) = (0, x))
    (hvertical : ∀ v, fderiv ℝ F (0, x) (0, v) = (0, v))
    (htime : ∀ᶠ q in 𝓝 (0, x), fderiv ℝ F q (1, 0) = (1, X (F q).2))
    (hfield : ∀ᶠ q in 𝓝 (0, x), fderiv ℝ F q (0, Z q) = (0, Y (F q).2)) :
    fderiv ℝ Z (0, x) (1, 0) = VectorField.lieBracket ℝ X Y x := by
  have hSX : DifferentiableAt ℝ (fun q : ℝ × E => ((1 : ℝ), X q.2)) (F (0, x)) := by
    rw [hbase]
    exact (differentiableAt_const (1 : ℝ)).prodMk (hX.comp _ differentiableAt_snd)
  have hVY : DifferentiableAt ℝ (fun q : ℝ × E => ((0 : ℝ), Y q.2)) (F (0, x)) := by
    rw [hbase]
    exact (differentiableAt_const (0 : ℝ)).prodMk (hY.comp _ differentiableAt_snd)
  have hh := fderiv_lieBracket_of_related hF (differentiableAt_const ((1 : ℝ), (0 : E)))
    ((differentiableAt_const (0 : ℝ)).prodMk hZ) hSX hVY htime hfield
  rw [lieBracket_time_vertical hZ, hvertical, hbase,
    lieBracket_suspended_vertical hX hY] at hh
  exact congrArg Prod.snd hh

end PolycyclicRecognition

end

end OAI
