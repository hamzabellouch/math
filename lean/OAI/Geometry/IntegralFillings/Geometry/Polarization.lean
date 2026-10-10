import Mathlib

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace SharpIntegralFillings
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma exists_bilinForm_of_parallelogram (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ B : LinearMap.BilinForm ℝ E, B.IsSymm ∧ B.toQuadraticMap.PosDef ∧
      (∀ v, B v v = (p v)^2) ∧
      ∀ u v, B u v = ((p (u+v))^2-(p (u-v))^2)/4 := by
  let : Norm E := ⟨p⟩
  let core : NormedSpace.Core ℝ E :=
    { norm_nonneg := fun v => apply_nonneg p v
      norm_smul := fun c v => map_smul_eq_mul p c v
      norm_triangle := fun x y => map_add_le_add p x y
      norm_eq_zero_iff := hp }
  let : NormedAddCommGroup E := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ E := NormedSpace.ofCore core
  have hparanorm : ∀ u v : E,
      ‖u+v‖*‖u+v‖+‖u-v‖*‖u-v‖ = 2*(‖u‖*‖u‖+‖v‖*‖v‖) := by
    intro u v
    change p (u+v)*p (u+v)+p (u-v)*p (u-v) = 2*(p u*p u+p v*p v)
    nlinarith [hpara u v]
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hparanorm
  refine ⟨innerₗ E,?_,?_,?_,?_⟩
  · exact ⟨fun u v => (real_inner_comm u v).symm⟩
  · intro v hv
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr hv
  · intro v
    change inner ℝ v v = (p v)^2
    exact real_inner_self_eq_norm_sq v
  · intro u v
    change inner ℝ u v = ((p (u+v))^2-(p (u-v))^2)/4
    have H := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) u v
    change inner ℝ u v = (p (u+v)*p (u+v)-p (u-v)*p (u-v))/4 at H
    simpa only [pow_two] using H

noncomputable def polarizationMatrix {ι : Type*} (p : Seminorm ℝ E) (b : ι → E) : Matrix ι ι ℝ :=
  fun i j => ((p (b i+b j))^2-(p (b i-b j))^2)/4

lemma polarizationMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    (polarizationMatrix p b).PosDef := by
  obtain ⟨B,hB,hpos,_,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b B hB).1 hpos

lemma polarizationMatrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : E) :
    (b.repr v) ⬝ᵥ (polarizationMatrix p b).mulVec (b.repr v) = (p v)^2 := by
  obtain ⟨B,_,_,hdiag,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  rw [←hdiag v]
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v v).symm

lemma measurable_polarizationMatrix {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] (p : A → Seminorm ℝ E) (b : ι → E)
    (hp : ∀ v, Measurable (fun x => p x v)) :
    ∀ i j, Measurable (fun x => polarizationMatrix (p x) b i j) := by
  intro i j
  exact ((hp _).pow_const 2 |>.sub ((hp _).pow_const 2)).div_const 4
end SharpIntegralFillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
