import Mathlib
import OAI.Analysis.Commutator.CornerAlgebra
import OAI.Analysis.Commutator.MatrixDiffuse

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixColumnCorner

variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CStarAlgebra D]

omit [Nonempty I] in
lemma minimal_projection (i : I) : IsStarProjection (Matrix.single i i (1:ℂ)) := by
  constructor <;> simp [IsIdempotentElem,IsSelfAdjoint,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]

omit [Nonempty I] in
lemma full_column (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i0 : I) :
    (∀ i j, star (φ (Matrix.single i i0 1))*φ (Matrix.single j i0 1)=
      if i=j then φ (Matrix.single i0 i0 1) else 0) ∧
    (∀ i, φ (Matrix.single i0 i0 1)*star (φ (Matrix.single i i0 1))=
      star (φ (Matrix.single i i0 1))) ∧
    ∑ i,φ (Matrix.single i i0 1)*star (φ (Matrix.single i i0 1))=1 := by
  constructor
  · intro i j
    rw [←map_star,←map_mul]
    by_cases hij : i=j
    · subst j; simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]
    · simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,hij]
  constructor
  · intro i
    rw [←map_star,←map_mul]
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]
  · simp only [←map_star,←map_mul,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,star_one,
      Matrix.single_mul_single_same,one_mul,←map_sum,Matrix.sum_single_one,map_one]

lemma trace_minimal [PartialOrder D] [StarOrderedRing D]
    (τ : D →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i : I) :
    τ (φ (Matrix.single i i 1))=(Fintype.card I : ℂ)⁻¹ :=
  MatrixDiffuse.diagonal_trace (τ.toLinearMap.comp φ.toLinearMap)
    (fun x y => by change τ (φ (x*y))=τ (φ (y*x)); simpa only [map_mul] using hτ (φ x) (φ y))
    (by change τ (φ 1)=1; simpa only [map_one] using h1) i

lemma exists_small_stage (J : ℕ → Type*) [∀ n, Fintype (J n)] [∀ n, Nonempty (J n)]
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (J m)) {β : ℝ} (hβ : 0<β) :
    ∃ n, (Fintype.card (J n) : ℝ)⁻¹ ≤ β := by
  obtain ⟨q,hq⟩ := exists_nat_gt β⁻¹
  obtain ⟨n,_,hn⟩ := hsize 0 q
  refine ⟨n,?_⟩
  have hcard : (0:ℝ)<Fintype.card (J n) := by exact_mod_cast Fintype.card_pos
  apply (inv_le_comm₀ hcard hβ).mpr
  exact hq.le.trans (by exact_mod_cast hn)

end Kadison.MatrixColumnCorner

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

lemma projection_symmetry_square : (p+p-1)*(p+p-1)=1 := by
  have h := hp.isIdempotentElem.eq
  noncomm_ring [h]

lemma projection_symmetry_selfadjoint : star (p+p-1)=p+p-1 := by
  simp only [star_sub,star_add,star_one,hp.isSelfAdjoint.star_eq]

def projectionSymmetry : unitary A :=
  ⟨p+p-1,by constructor <;> rw [projection_symmetry_selfadjoint hp,projection_symmetry_square hp]⟩

@[simp] lemma projectionSymmetry_coe : (projectionSymmetry hp : A)=p+p-1 := rfl

lemma projectionSymmetry_half : p=(1/2:ℂ) • (1+(projectionSymmetry hp:A)) := by
  rw [projectionSymmetry_coe,show (1:A)+(p+p-1)=p+p by abel,←two_smul ℂ p,smul_smul]
  norm_num

lemma projectionSymmetry_left : p*(projectionSymmetry hp:A)=p := by
  rw [projectionSymmetry_coe,mul_sub,mul_add,hp.isIdempotentElem.eq,mul_one]
  abel

lemma projectionSymmetry_right : (projectionSymmetry hp:A)*p=p := by
  rw [projectionSymmetry_coe,sub_mul,add_mul,hp.isIdempotentElem.eq,one_mul]
  abel

omit hp in
lemma unitary_dihedral {d s : unitary A} (hd : (d:A)*(d:A)=1) (hs : (s:A)*(s:A)=1) :
    MulAut.conj d (d*s)=(d*s)⁻¹ := by
  have hd' : d*d=1 := Subtype.ext hd
  have hs' : s*s=1 := Subtype.ext hs
  have hdi : d⁻¹=d := inv_eq_of_mul_eq_one_right hd'
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right hs'
  simp only [MulAut.conj_apply,mul_inv_rev,hdi,hsi]
  rw [←mul_assoc,hd',one_mul]

lemma isStarProjection_corner {e : Corner hp} (he : IsStarProjection (e:A)) :
    IsStarProjection e := by
  constructor
  · exact Subtype.ext he.isIdempotentElem.eq
  · exact Subtype.ext he.isSelfAdjoint.star_eq

end Kadison

end

end
end

end OAI
