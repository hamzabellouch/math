import Mathlib
import OAI.Geometry.Borsuk.Support.Chambers

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section DisjointChambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma compact_disjoint_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧
      (Pairwise (fun c d : ↥C => Disjoint (interior (signChamber Z c.val))
        (interior (signChamber Z d.val)))) ∧
      K ⊆ ⋃ c : ↥C, interior (signChamber Z c.val) := by
  classical
  obtain ⟨C,hCK,hcover⟩ := compact_finite_chambers hK hsub
  let g : E → Set E := fun c => interior (signChamber Z c)
  have hsurj : (↑C : Set E).SurjOn g (↑(C.image g) : Set (Set E)) := by
    intro U hU
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hU
    exact ⟨c,hc,rfl⟩
  obtain ⟨D,hDC,hDinj,hDimage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑C : Set E) (C.image g) hsurj
  refine ⟨D,fun c hc => hCK (hDC hc),?_,?_⟩
  · intro c d hne
    rcases signChamber_eq_or_disjoint Z c.val d.val with he | hdj
    · exfalso
      exact hne (Subtype.ext (hDinj c.property d.property (congrArg interior he)))
    · exact hdj.mono interior_subset interior_subset
  · intro x hx
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hg : g c ∈ D.image g := by rw [hDimage]; exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    obtain ⟨d,hd,hgd⟩ := Finset.mem_image.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨d,hd⟩,by change x ∈ g d; rw [hgd]; exact hxc⟩
end DisjointChambers
end BorsukNine

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixEmbedding
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

lemma toEuclideanLin_mul {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    Matrix.toEuclideanLin (A*B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((A*B)*ᵥ v) i = (A *ᵥ (B *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]

noncomputable def isometryMatrix (e : D →ₗᵢ[ℝ] E) : Matrix ν μ ℝ :=
  Matrix.toEuclideanLin.symm e.toLinearMap

omit [DecidableEq ν] in
lemma isometryMatrix_action (e : D →ₗᵢ[ℝ] E) (x : D) :
    Matrix.toEuclideanLin (isometryMatrix e) x = e x :=
  LinearMap.congr_fun (Matrix.toEuclideanLin.apply_symm_apply e.toLinearMap) x

lemma isometryMatrix_star_mul (e : D →ₗᵢ[ℝ] E) :
    (isometryMatrix e)ᴴ * isometryMatrix e = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have he : Matrix.toEuclideanLin (isometryMatrix e) = e.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [he]
  rw [e.adjoint_comp_self']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.id_apply,Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]

noncomputable def matrixEmbed (e : D →ₗᵢ[ℝ] E) : Matrix μ μ ℝ →ₗ[ℝ] Matrix ν ν ℝ where
  toFun B := isometryMatrix e * B * (isometryMatrix e)ᴴ
  map_add' B C := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t B := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl

omit [DecidableEq ν] in
lemma matrixEmbed_nonneg (e : D →ₗᵢ[ℝ] E) {B : Matrix μ μ ℝ} (hB : 0 ≤ B) :
    0 ≤ matrixEmbed e B := ((Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same _).nonneg

lemma matrixEmbed_trace (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) :
    Matrix.trace (matrixEmbed e B) = Matrix.trace B := by
  change Matrix.trace (isometryMatrix e * B * (isometryMatrix e)ᴴ) = Matrix.trace B
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,isometryMatrix_star_mul,Matrix.one_mul]

lemma matrixEmbed_action (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) (x : D) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) (e x) =
      e (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ) B x) := by
  change Matrix.toEuclideanLin (matrixEmbed e B) (e x) = e (Matrix.toEuclideanLin B x)
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) (e x) = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)
    (Matrix.toEuclideanLin B (Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x))) = _
  have hh : Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
    rw [← isometryMatrix_action e x]
    change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
      (Matrix.toEuclideanLin (isometryMatrix e))) x = x
    rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
    simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
  rw [hh,isometryMatrix_action]

lemma matrixEmbed_kernel (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) {u : E}
    (hu : ∀ x : D, ⟪u,e x⟫ = 0) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) u = 0 := by
  have hz : Matrix.toEuclideanLin (isometryMatrix e)ᴴ u = 0 := by
    apply ext_inner_left ℝ
    intro x
    rw [inner_zero_right,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint u⟫ = 0
    rw [LinearMap.adjoint_inner_right,isometryMatrix_action,real_inner_comm]
    exact hu x
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) u = 0
  rw [toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e * B) (Matrix.toEuclideanLin (isometryMatrix e)ᴴ u) = 0
  rw [hz,map_zero]

end MatrixEmbedding
end BorsukNine

end OAI
