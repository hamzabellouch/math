import OAI.Analysis.KadisonKastler.PointedMatrixProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # The four-dimensional pointed matrix state

Left and right matrix multiplication act on the Hilbert space of two by
two matrices. The square root of the diagonal density is cyclic for
both actions. An orthonormal basis beginning at that vector makes the
reference vector the zero-coordinate vacuum used by the infinite product.
-/

namespace KadisonKastler

noncomputable section

abbrev PointedLocalHilbert := EuclideanSpace ℂ (Fin 4)

def pointedLocalVacuum : PointedLocalHilbert := EuclideanSpace.single 0 1

structure PointedLocalMatrixData (ν : ℝ) where
  left : Generator.MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
  right : Generator.MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
  commutes : ∀ i j k l, Commute (left.entry i j) (right.entry k l)
  left_spans : Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
    left.entry ij.1 ij.2 pointedLocalVacuum)) = ⊤
  right_spans : Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
    right.entry ij.1 ij.2 pointedLocalVacuum)) = ⊤
  moment : ∀ i j, inner ℂ pointedLocalVacuum (left.entry i j pointedLocalVacuum) =
    if i = j then (twoSiteWeight ν i : ℂ) else 0

abbrev PointedRawHilbert := EuclideanSpace ℂ (Fin 2 × Fin 2)

def pointedRawLeft (i j : Fin 2) : PointedRawHilbert →L[ℂ] PointedRawHilbert :=
  LinearMap.toContinuousLinearMap
    { toFun x := WithLp.toLp 2 (fun p => if p.1 = i then x (j, p.2) else 0)
      map_add' x y := by ext p; by_cases h : p.1 = i <;> simp [h]
      map_smul' c x := by ext p; simp }

@[simp] theorem pointedRawLeft_apply (i j : Fin 2) (x : PointedRawHilbert)
    (p : Fin 2 × Fin 2) : pointedRawLeft i j x p = if p.1 = i then x (j, p.2) else 0 := rfl

def pointedRawRight (i j : Fin 2) : PointedRawHilbert →L[ℂ] PointedRawHilbert :=
  LinearMap.toContinuousLinearMap
    { toFun x := WithLp.toLp 2 (fun p => if p.2 = i then x (p.1, j) else 0)
      map_add' x y := by ext p; by_cases h : p.2 = i <;> simp [h]
      map_smul' c x := by ext p; simp }

@[simp] theorem pointedRawRight_apply (i j : Fin 2) (x : PointedRawHilbert)
    (p : Fin 2 × Fin 2) : pointedRawRight i j x p = if p.2 = i then x (p.1, j) else 0 := rfl

theorem pointedRawLeft_star (i j : Fin 2) : star (pointedRawLeft i j) = pointedRawLeft j i := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawLeft_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem pointedRawRight_star (i j : Fin 2) : star (pointedRawRight i j) = pointedRawRight j i := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawRight_apply]
  fin_cases i <;> fin_cases j <;> simp

def pointedRawLeftUnits : Generator.MatrixUnitSystem (Fin 2)
    (PointedRawHilbert →L[ℂ] PointedRawHilbert) where
  entry := pointedRawLeft
  star_entry := pointedRawLeft_star
  mul_entry i j k l := by
    ext x p
    simp only [mul_apply_eq_comp, pointedRawLeft_apply]
    split_ifs <;> simp_all
  total := by
    ext x p
    simp only [Fin.sum_univ_two, add_apply,
      one_apply_eq_self]
    rcases p with ⟨p, q⟩
    fin_cases p <;> simp

def pointedRawRightUnits : Generator.MatrixUnitSystem (Fin 2)
    (PointedRawHilbert →L[ℂ] PointedRawHilbert) where
  entry := pointedRawRight
  star_entry := pointedRawRight_star
  mul_entry i j k l := by
    ext x p
    simp only [mul_apply_eq_comp, pointedRawRight_apply]
    split_ifs <;> simp_all
  total := by
    ext x p
    simp only [Fin.sum_univ_two, add_apply,
      one_apply_eq_self]
    rcases p with ⟨p, q⟩
    fin_cases q <;> simp

theorem pointedRawUnits_commute (i j k l : Fin 2) :
    Commute (pointedRawLeft i j) (pointedRawRight k l) := by
  ext x p
  simp only [mul_apply_eq_comp, pointedRawLeft_apply, pointedRawRight_apply]
  split_ifs <;> rfl

def pointedRawVacuum (ν : ℝ) : PointedRawHilbert :=
  WithLp.toLp 2 (fun p => if p.1 = p.2 then (Real.sqrt (twoSiteWeight ν p.1) : ℂ) else 0)

@[simp] theorem pointedRawVacuum_apply (ν : ℝ) (p : Fin 2 × Fin 2) :
    pointedRawVacuum ν p =
      if p.1 = p.2 then (Real.sqrt (twoSiteWeight ν p.1) : ℂ) else 0 := rfl

theorem twoSiteWeight_pos {ν : ℝ} (hν : 0 < ν) (i : Fin 2) : 0 < twoSiteWeight ν i := by
  fin_cases i <;> simp only [twoSiteWeight, Fin.zero_eta, ↓reduceIte]
  · positivity
  · positivity

theorem twoSiteWeight_sum {ν : ℝ} (hν : 0 < ν) :
    twoSiteWeight ν 0 + twoSiteWeight ν 1 = 1 := by
  simp only [twoSiteWeight, ↓reduceIte, one_ne_zero]
  field_simp

theorem pointedRawLeft_vacuum (ν : ℝ) (i j : Fin 2) :
    pointedRawLeft i j (pointedRawVacuum ν) =
      (Real.sqrt (twoSiteWeight ν j) : ℂ) • EuclideanSpace.single (i,j) 1 := by
  ext p
  rcases p with ⟨p,q⟩
  simp only [pointedRawLeft_apply, pointedRawVacuum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
  by_cases h : p = i <;> by_cases h' : q = j <;> simp_all [eq_comm]

theorem pointedRawRight_vacuum (ν : ℝ) (i j : Fin 2) :
    pointedRawRight i j (pointedRawVacuum ν) =
      (Real.sqrt (twoSiteWeight ν j) : ℂ) • EuclideanSpace.single (j,i) 1 := by
  ext p
  rcases p with ⟨p,q⟩
  simp only [pointedRawRight_apply, pointedRawVacuum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
  by_cases h : p = j <;> by_cases h' : q = i <;> simp_all

theorem pointedRawLeft_moment {ν : ℝ} (hν : 0 < ν) (i j : Fin 2) :
    inner ℂ (pointedRawVacuum ν) (pointedRawLeft i j (pointedRawVacuum ν)) =
      if i = j then (twoSiteWeight ν i : ℂ) else 0 := by
  rw [pointedRawLeft_vacuum, inner_smul_right, EuclideanSpace.inner_single_right]
  by_cases h : i = j
  · subst j
    simp only [pointedRawVacuum_apply, ↓reduceIte, one_mul,
      Complex.conj_ofReal]
    norm_cast
    exact Real.mul_self_sqrt (twoSiteWeight_pos hν i).le
  · simp [pointedRawVacuum_apply, h]

theorem pointedRawVacuum_norm {ν : ℝ} (hν : 0 < ν) : ‖pointedRawVacuum ν‖ = 1 := by
  have hn : ‖pointedRawVacuum ν‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawVacuum_apply]
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (twoSiteWeight_pos hν 0).le,
      Real.sq_sqrt (twoSiteWeight_pos hν 1).le, twoSiteWeight_sum hν]
  nlinarith [norm_nonneg (pointedRawVacuum ν)]

private theorem span_of_basis_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (b : Module.Basis ι ℂ V) (W : Submodule ℂ V) (h : ∀ i, b i ∈ W) :
    W = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)

theorem pointedRawLeft_spans {ν : ℝ} (hν : 0 < ν) :
    Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawLeft ij.1 ij.2 (pointedRawVacuum ν))) = ⊤ := by
  apply span_of_basis_mem (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis
  rintro ⟨i,j⟩
  change (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ) (i,j) ∈ _
  rw [EuclideanSpace.basisFun_apply]
  have hc : (Real.sqrt (twoSiteWeight ν j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (twoSiteWeight_pos hν j))
  have hm := Submodule.subset_span (R := ℂ) (Set.mem_range_self (i,j) :
    pointedRawLeft i j (pointedRawVacuum ν) ∈ Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawLeft ij.1 ij.2 (pointedRawVacuum ν)))
  rw [pointedRawLeft_vacuum] at hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using Submodule.smul_mem _ (Real.sqrt (twoSiteWeight ν j) : ℂ)⁻¹ hm

theorem pointedRawRight_spans {ν : ℝ} (hν : 0 < ν) :
    Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawRight ij.1 ij.2 (pointedRawVacuum ν))) = ⊤ := by
  apply span_of_basis_mem (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis
  rintro ⟨i,j⟩
  change (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ) (i,j) ∈ _
  rw [EuclideanSpace.basisFun_apply]
  have hc : (Real.sqrt (twoSiteWeight ν i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (twoSiteWeight_pos hν i))
  have hm := Submodule.subset_span (R := ℂ) (Set.mem_range_self (j,i) :
    pointedRawRight j i (pointedRawVacuum ν) ∈ Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawRight ij.1 ij.2 (pointedRawVacuum ν)))
  rw [pointedRawRight_vacuum] at hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using Submodule.smul_mem _ (Real.sqrt (twoSiteWeight ν i) : ℂ)⁻¹ hm

private theorem exists_pointedRaw_basis {ν : ℝ} (hν : 0 < ν) :
    ∃ b : OrthonormalBasis (Fin 4) ℂ PointedRawHilbert, b 0 = pointedRawVacuum ν := by
  have hv : Orthonormal ℂ (({0} : Set (Fin 4)).domRestrict
      (fun _ => pointedRawVacuum ν)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact pointedRawVacuum_norm hν
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [PointedRawHilbert])
  exact ⟨b, hb 0 (by simp)⟩

private theorem span_linearEquiv_image {V W ι : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (v : ι → V) (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range (fun i => e (v i))) = ⊤ := by
  have hr : Set.range (fun i => e (v i)) = e.toLinearMap '' Set.range v := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨v i, ⟨i,rfl⟩, rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [hr, ← Submodule.map_span, hv]
  exact (Submodule.map_top e.toLinearMap).trans
    (LinearMap.range_eq_top.mpr e.surjective)

/-- The two faithful matrix actions with the designated vacuum vector. -/
theorem exists_pointedLocalMatrixData {ν : ℝ} (hν : 0 < ν) :
    Nonempty (PointedLocalMatrixData ν) := by
  obtain ⟨b,hb⟩ := exists_pointedRaw_basis hν
  let e : PointedRawHilbert ≃ₗᵢ[ℂ] PointedLocalHilbert := b.repr
  have he : e (pointedRawVacuum ν) = pointedLocalVacuum := by
    rw [← hb]
    exact b.repr_self 0
  have hs : e.symm pointedLocalVacuum = pointedRawVacuum ν := by
    rw [← he, e.symm_apply_apply]
  refine ⟨{
    left := pointedRawLeftUnits.map e.conjStarAlgEquiv.toStarAlgHom
    right := pointedRawRightUnits.map e.conjStarAlgEquiv.toStarAlgHom
    commutes := ?_
    left_spans := ?_
    right_spans := ?_
    moment := ?_ }⟩
  · intro i j k l
    exact (pointedRawUnits_commute i j k l).map e.conjStarAlgEquiv.toMonoidHom
  · change Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      e.conjStarAlgEquiv (pointedRawLeft ij.1 ij.2) pointedLocalVacuum)) = ⊤
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
    exact span_linearEquiv_image e.toLinearEquiv _ (pointedRawLeft_spans hν)
  · change Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      e.conjStarAlgEquiv (pointedRawRight ij.1 ij.2) pointedLocalVacuum)) = ⊤
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
    exact span_linearEquiv_image e.toLinearEquiv _ (pointedRawRight_spans hν)
  · intro i j
    change inner ℂ pointedLocalVacuum
      (e.conjStarAlgEquiv (pointedRawLeft i j) pointedLocalVacuum) = _
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs, ← he, e.inner_map_map]
    exact pointedRawLeft_moment hν i j

end

end KadisonKastler

end OAI
