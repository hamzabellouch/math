import Mathlib
import OAI.Algebra.MarkedTensor.MatrixIdeals

namespace OAI

/-! Traceless matrix coordinates, adjoint actions and base change of spanning families. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators commutatorElement
variable {R : Type*} [CommRing R]
abbrev Mat₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev Vec₃ (R : Type*) := Fin 3 → R

noncomputable def half [Algebra ℚ R] : R := algebraMap ℚ R (1/2)
lemma two_half [Algebra ℚ R] : (2:R)*half = 1 := by
  simpa only [half, map_mul, map_ofNat, map_one] using
    congrArg (algebraMap ℚ R) (show (2:ℚ)*(1/2)=1 by norm_num)
noncomputable def traceless (v : Vec₃ R) : Mat₂ R := !![v 1, v 0; v 2, -v 1]
noncomputable def coordinates [Algebra ℚ R] (A : Mat₂ R) : Vec₃ R :=
  ![A 0 1, (A 0 0-A 1 1)*half, A 1 0]

def extract (A : Mat₂ R) : Vec₃ R := ![A 0 1,A 0 0,A 1 0]

lemma scalar_lie (A B : Mat₂ R) (a b : R) :
    lie (A-scalar (Fin 2) a) (B-scalar (Fin 2) b) = lie A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lie, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal] <;> ring

lemma scalar_lie_left (A B : Mat₂ R) (a : R) :
    lie (A-scalar (Fin 2) a) B = lie A B := by
  simpa only [map_zero, sub_zero] using scalar_lie A B a 0

lemma traceless_coordinates [Algebra ℚ R] (A : Mat₂ R) :
    traceless (coordinates A) = A-scalar (Fin 2) (Matrix.trace A*half) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceless, coordinates, Matrix.trace, Fin.sum_univ_two, Matrix.scalar,
      Matrix.diagonal]
  · linear_combination A 0 0 * two_half (R := R)
  · linear_combination A 1 1 * two_half (R := R)

lemma traceless_extract (v : Vec₃ R) : extract (traceless v) = v := by
  ext i; fin_cases i <;> simp [extract, traceless]

lemma extract_traceless (A : Mat₂ R) (hA : Matrix.trace A=0) :
    traceless (extract A) = A := by
  have hdiag : A 0 0+A 1 1=0 := by simpa [Matrix.trace, Fin.sum_univ_two] using hA
  ext i j; fin_cases i <;> fin_cases j <;> simp [traceless,extract]
  exact neg_eq_of_add_eq_zero_right hdiag

noncomputable def tracelessLM : Vec₃ R →ₗ[R] Mat₂ R where
  toFun := traceless
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [traceless, add_comm]
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> simp [traceless]

def extractLM : Mat₂ R →ₗ[R] Vec₃ R where
  toFun := extract
  map_add' x y := by ext i; fin_cases i <;> simp [extract]
  map_smul' c x := by ext i; fin_cases i <;> simp [extract]

noncomputable def conjugationLM (g : SpecialLinearGroup (Fin 2) R) : Mat₂ R →ₗ[R] Mat₂ R where
  toFun A := mat g*A*mat g⁻¹
  map_add' A B := by simp only [mul_add,add_mul]
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc, RingHom.id_apply]

noncomputable def adjoint (g : SpecialLinearGroup (Fin 2) R) :
    Vec₃ R →ₗ[R] Vec₃ R := extractLM ∘ₗ conjugationLM g ∘ₗ tracelessLM

lemma traceless_adjoint (g : SpecialLinearGroup (Fin 2) R) (v : Vec₃ R) :
    traceless (adjoint g v) = mat g*traceless v*mat g⁻¹ := by
  apply extract_traceless
  change Matrix.trace (mat g*traceless v*mat g⁻¹)=0
  rw [Matrix.trace_mul_cycle]
  simp only [← mat_mul, inv_mul_cancel, mat_one, one_mul]
  simp [Matrix.trace, Fin.sum_univ_two, traceless]

lemma conjugate_scalar (g : SpecialLinearGroup (Fin 2) R) (A : Mat₂ R) (a : R) :
    mat g*(A-scalar (Fin 2) a)*mat g⁻¹ =
      mat g*A*mat g⁻¹-scalar (Fin 2) a := by
  rw [mul_sub,sub_mul]
  have hs : mat g*scalar (Fin 2) a*mat g⁻¹ = scalar (Fin 2) a := by
    have hsc : mat g*scalar (Fin 2) a = a • mat g := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
    rw [hsc, smul_mul_assoc, ← mat_mul, mul_inv_cancel, mat_one]
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply]
  rw [hs]

lemma reference_traceless_triple [Algebra ℚ R] {m N : Ideal R} (hNm : N ≤ m)
    {u v w U V W z t s : SpecialLinearGroup (Fin 2) R}
    (hu : mat u-mat U ∈ m.matrix (Fin 2)) (hv : mat v-mat V ∈ m.matrix (Fin 2))
    (hw : mat w-mat W ∈ m.matrix (Fin 2))
    (hz : mat z-1 ∈ N.matrix (Fin 2)) (ht : mat t-1 ∈ N.matrix (Fin 2))
    (hs : mat s-1 ∈ N.matrix (Fin 2))
    (hrel : ⁅u*z*u⁻¹,⁅v*t*v⁻¹,w*s*w⁻¹⁆⁆=1) :
    lie (traceless (adjoint U (coordinates (mat z-1))))
      (lie (traceless (adjoint V (coordinates (mat t-1))))
        (traceless (adjoint W (coordinates (mat s-1))))) ∈ (m*N^3).matrix (Fin 2) := by
  rw [traceless_adjoint, traceless_adjoint, traceless_adjoint,
    traceless_coordinates, traceless_coordinates, traceless_coordinates,
    conjugate_scalar, conjugate_scalar, conjugate_scalar, scalar_lie, scalar_lie_left]
  exact reference_triple_mem hNm hu hv hw hz ht hs hrel

end BoundaryOnly.Holonomy

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators
variable {K R H : Type*} [CommRing K] [CommRing R] [Algebra K R]

lemma matrix_span_base_change (A : H → Matrix (Fin 3) (Fin 3) K)
    (hA : Submodule.span K (Set.range A) = ⊤) :
    Submodule.span R (Set.range (fun h ↦ (A h).map (algebraMap K R))) = ⊤ := by
  let S := Submodule.span R (Set.range (fun h ↦ (A h).map (algebraMap K R)))
  have hmap (B : Matrix (Fin 3) (Fin 3) K) : B.map (algebraMap K R) ∈ S := by
    have hB : B ∈ Submodule.span K (Set.range A) := by rw [hA]; trivial
    induction hB using Submodule.span_induction with
    | mem B hB =>
        obtain ⟨h,rfl⟩ := hB
        exact Submodule.subset_span ⟨h,rfl⟩
    | zero => simp
    | add B C hB hC ihB ihC =>
        simpa only [Matrix.map_add _ (map_add (algebraMap K R))] using S.add_mem ihB ihC
    | smul c B hB ih =>
        have he : (c • B).map (algebraMap K R) =
            algebraMap K R c • B.map (algebraMap K R) := by
          ext i j; simp [smul_eq_mul]
        rw [he]
        exact S.smul_mem _ ih
  have hsingle (i j : Fin 3) : Matrix.single i j (1:R) ∈ S := by
    simpa using hmap (Matrix.single i j (1:K))
  apply top_unique
  intro B _
  rw [Matrix.matrix_eq_sum_single B]
  apply S.sum_mem; intro i _
  apply S.sum_mem; intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using S.smul_mem (B i j) (hsingle i j)

lemma adjoint_matrix_map (g : SpecialLinearGroup (Fin 2) K) :
    LinearMap.toMatrix' (adjoint (SpecialLinearGroup.map (algebraMap K R) g)) =
      (LinearMap.toMatrix' (adjoint g)).map (algebraMap K R) := by
  have hinv : mat ((SpecialLinearGroup.map (algebraMap K R) g)⁻¹) =
      (mat g⁻¹).map (algebraMap K R) := by rw [← map_inv]; rfl
  have hmat : mat (SpecialLinearGroup.map (algebraMap K R) g) =
      (mat g).map (algebraMap K R) := rfl
  ext i j
  change extract (mat (SpecialLinearGroup.map (algebraMap K R) g) *
      traceless (Pi.single j 1) * mat ((SpecialLinearGroup.map (algebraMap K R) g)⁻¹)) i =
      algebraMap K R (extract (mat g * traceless (Pi.single j 1) * mat g⁻¹) i)
  rw [hmat, hinv]
  fin_cases i <;> fin_cases j <;>
    simp [extract, traceless, Matrix.mul_apply, Fin.sum_univ_two]

 

lemma adjoint_span_base_change (G : H → SpecialLinearGroup (Fin 2) K)
    (hG : Submodule.span K (Set.range (fun h ↦ adjoint (G h))) = ⊤) :
    Submodule.span R (Set.range (fun h ↦ adjoint
      (SpecialLinearGroup.map (algebraMap K R) (G h)))) = ⊤ := by
  have hM : Submodule.span K (Set.range (fun h ↦ LinearMap.toMatrix' (adjoint (G h)))) = ⊤ := by
    have h := congrArg (Submodule.map LinearMap.toMatrix'.toLinearMap) hG
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearEquiv.range, Function.comp_def, LinearEquiv.coe_coe] using h
  have h := matrix_span_base_change (R := R) _ hM
  have h' := congrArg (Submodule.map Matrix.toLin'.toLinearMap) h
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearEquiv.range, ← adjoint_matrix_map, LinearMap.toMatrix'_symm,
    LinearEquiv.symm_apply_apply, Function.comp_def, LinearEquiv.coe_coe,
    Matrix.toLin'_toMatrix'] using h'

end BoundaryOnly.Holonomy
end

end OAI
