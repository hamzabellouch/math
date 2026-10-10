import Mathlib
import OAI.Probability.SKValue.GroundState.AffineComparison

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable {κ : Type*} [Fintype κ]

noncomputable def columnResidual (v w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
  w-⟪v,w⟫ • v

noncomputable def columnVector (v w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
  ⟪v,w⟫ • columnResidual v w + (⟪v,w⟫^2/Real.sqrt 2) • v

noncomputable def quadraticCoeff (w : EuclideanSpace ℝ κ) (k : κ×κ) : ℝ :=
  w k.1*w k.2/Real.sqrt 2

noncomputable def columnSplitCoeff (v w : EuclideanSpace ℝ κ) : κ ⊕ (κ×κ) → ℝ :=
  Sum.elim (fun k ↦ columnVector v w k) (quadraticCoeff (columnResidual v w))

lemma euclidean_inner_sum (x y : EuclideanSpace ℝ κ) :
    ⟪x,y⟫=∑ k,x k*y k := by
  simp only [PiLp.inner_apply,Real.inner_apply]

lemma columnResidual_inner {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w w' : EuclideanSpace ℝ κ) :
    ⟪columnResidual v w,columnResidual v w'⟫=⟪w,w'⟫-⟪v,w⟫*⟪v,w'⟫ := by
  simp only [columnResidual,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,hv]
  rw [real_inner_comm w v]
  ring

lemma columnResidual_orthogonal {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w : EuclideanSpace ℝ κ) : ⟪v,columnResidual v w⟫=0 := by
  simp only [columnResidual,inner_sub_right,real_inner_smul_right,hv,mul_one,sub_self]

lemma quadraticCoeff_inner (x y : EuclideanSpace ℝ κ) :
    (∑ k,quadraticCoeff x k*quadraticCoeff y k)=⟪x,y⟫^2/2 := by
  have hs : Real.sqrt 2 ^ 2=2 := Real.sq_sqrt (by norm_num)
  calc
    _ = (∑ k : κ×κ,(x k.1*x k.2)*(y k.1*y k.2))/(Real.sqrt 2)^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [quadraticCoeff]
      ring
    _ = _ := by rw [product_inner_sum,←euclidean_inner_sum,hs]; ring

lemma columnVector_inner {v : EuclideanSpace ℝ κ} (hv : ⟪v,v⟫=1)
    (w w' : EuclideanSpace ℝ κ) :
    ⟪columnVector v w,columnVector v w'⟫=
      ⟪v,w⟫*⟪v,w'⟫*(⟪w,w'⟫-⟪v,w⟫*⟪v,w'⟫)+⟪v,w⟫^2*⟪v,w'⟫^2/2 := by
  have hs : Real.sqrt 2 ^ 2=2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have ho := columnResidual_orthogonal hv w
  have ho' := columnResidual_orthogonal hv w'
  have hor : ⟪columnResidual v w,v⟫=0 := by rwa [real_inner_comm]
  simp only [columnVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,ho',hor,hv,columnResidual_inner hv]
  field_simp
  ring_nf
  simp only [hs]
  ring

lemma columnSplitCoeff_inner {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w w' : EuclideanSpace ℝ κ) :
    (∑ k,columnSplitCoeff v w k*columnSplitCoeff v w' k)=
      ∑ k,quadraticCoeff w k*quadraticCoeff w' k := by
  rcases hv with rfl|hv
  · simp [columnSplitCoeff,columnVector,columnResidual,Fintype.sum_sum_type]
  · rw [Fintype.sum_sum_type]
    simp only [columnSplitCoeff,Sum.elim_inl,Sum.elim_inr]
    rw [←euclidean_inner_sum,columnVector_inner hv,quadraticCoeff_inner,
      columnResidual_inner hv,quadraticCoeff_inner]
    ring

lemma columnSplitCoeff_distance {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w w' : EuclideanSpace ℝ κ) :
    (∑ k,(columnSplitCoeff v w k-columnSplitCoeff v w' k)^2)=
      ∑ k,(quadraticCoeff w k-quadraticCoeff w' k)^2 := by
  rw [sq_distance_sum,sq_distance_sum]
  simp only [sq]
  rw [columnSplitCoeff_inner hv,columnSplitCoeff_inner hv,columnSplitCoeff_inner hv]

theorem expected_max_column_split {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) (hv : v=0 ∨ ⟪v,v⟫=1) :
    (∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i)
       ∂gaussianProduct (κ×κ))=
    ∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i)
       ∂gaussianProduct (κ ⊕ (κ×κ)) := by
  apply le_antisymm
  · exact expected_affine_max_le _ _ d (fun i j ↦ (columnSplitCoeff_distance hv (w i) (w j)).symm.le)
  · exact expected_affine_max_le _ _ d (fun i j ↦ (columnSplitCoeff_distance hv (w i) (w j)).le)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

noncomputable def quadraticValue (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ) : ℝ :=
  ∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i)
     ∂gaussianProduct (κ×κ)

omit [Fintype ι] [Nonempty ι] in
lemma linearProcess_integral_zero [Fintype ι] [Nonempty ι] {ν : Type*} [Fintype ν]
    (a : ι → ν → ℝ) (i : ι) :
    (∫ z,linearProcess a z i ∂gaussianProduct ν)=0 := by
  simp only [linearProcess]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k _
    rw [integral_const_mul]
    simp [gaussianProduct,standardGaussian,integral_eval]
  · intro k _
    exact (gaussian_coordinate_integrable k).const_mul _

lemma quadraticValue_ge_offset (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ) (i : ι) :
    d i≤quadraticValue w d := by
  have h := integral_mono
    ((linearProcess_integrable (fun i ↦ quadraticCoeff (w i)) i).add (integrable_const (d i)))
    (affineMaximum_integrable (fun i ↦ quadraticCoeff (w i)) d)
    (fun z ↦ le_finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i) i)
  simp only [Pi.add_apply] at h
  rw [integral_add (linearProcess_integrable _ _) (integrable_const _),
    linearProcess_integral_zero,integral_const,probReal_univ,one_smul,zero_add] at h
  exact h

lemma column_product_integrable (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) :
    Integrable (fun p : (κ → ℝ)×((κ×κ) → ℝ) ↦
      finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (columnResidual v (w i))) p.2 i+
        (d i+linearProcess (fun i k ↦ columnVector v (w i) k) p.1 i)))
      ((gaussianProduct κ).prod (gaussianProduct (κ×κ))) := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)
  have hi := affineMaximum_integrable (fun i ↦ columnSplitCoeff v (w i)) d
  have h := (he.integrable_comp hi.aestronglyMeasurable).2 hi
  change Integrable _ ((gaussianProduct κ).prod (gaussianProduct (κ×κ))) at h
  convert h using 1
  ext p
  congr 1
  ext i
  simp [linearProcess,columnSplitCoeff,Fintype.sum_sum_type,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  ring

theorem quadraticValue_column (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) (hv : v=0 ∨ ⟪v,v⟫=1) :
    quadraticValue w d =
      ∫ z,quadraticValue (fun i ↦ columnResidual v (w i))
        (fun i ↦ d i+linearProcess (fun i k ↦ columnVector v (w i) k) z i)
        ∂gaussianProduct κ := by
  unfold quadraticValue
  rw [expected_max_column_split w d v hv]
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)
  change (∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i)
    ∂Measure.pi (fun _ : κ ⊕ (κ×κ) ↦ standardGaussian)) = _
  rw [←he.integral_comp' (fun z ↦ finiteMaximum (fun i ↦
    linearProcess (fun i ↦ columnSplitCoeff v (w i)) z i+d i))]
  have heq (p : (κ → ℝ)×((κ×κ) → ℝ)) :
      (fun i ↦ linearProcess (fun i ↦ columnSplitCoeff v (w i))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ (κ×κ) ↦ ℝ)).symm p) i+d i)=
      (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (columnResidual v (w i))) p.2 i+
        (d i+linearProcess (fun i k ↦ columnVector v (w i) k) p.1 i)) := by
    ext i
    simp [linearProcess,columnSplitCoeff,Fintype.sum_sum_type,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm,Sum.elim_inl,Sum.elim_inr]
    ring
  simp only [heq]
  exact integral_prod _ (column_product_integrable w d v)

lemma column_integral_integrable (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ)
    (v : EuclideanSpace ℝ κ) :
    Integrable (fun z ↦ quadraticValue (fun i ↦ columnResidual v (w i))
        (fun i ↦ d i+linearProcess (fun i k ↦ columnVector v (w i) k) z i))
        (gaussianProduct κ) := (column_product_integrable w d v).integral_prod_left

end SKValueG

end

end OAI
