import OAI.Algebra.Finitistic.Encoding.RelationBasisCoefficients

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.EncodingGenerators
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The entire first arrow space inside the encoding algebra. -/
def first : Arrows k d →ₗ[k] B P where
  toFun x := (0,0,0,x,0,0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The entire second arrow space inside the encoding algebra. -/
def second : Arrows k d →ₗ[k] B P where
  toFun x := (0,0,0,0,x,0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

lemma first_mem (S : Subalgebra k (B P)) (h : ∀ a, arrow01 P a ∈ S)
    (x : Arrows k d) : first P x ∈ S := by
  have hx := congrArg (first P) ((Pi.basisFun k (Fin (d+1))).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  exact S.sum_mem fun a _ => by
    simpa only [map_smul, Pi.basisFun_apply, first, LinearMap.coe_mk,
      AddHom.coe_mk, arrow01, basis] using S.smul_mem (h a) (((Pi.basisFun k (Fin (d+1))).repr x) a)

lemma second_mem (S : Subalgebra k (B P)) (h : ∀ a, arrow12 P a ∈ S)
    (x : Arrows k d) : second P x ∈ S := by
  have hx := congrArg (second P) ((Pi.basisFun k (Fin (d+1))).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  exact S.sum_mem fun a _ => by
    simpa only [map_smul, Pi.basisFun_apply, second, LinearMap.coe_mk,
      AddHom.coe_mk, arrow12, basis] using S.smul_mem (h a) (((Pi.basisFun k (Fin (d+1))).repr x) a)

lemma path_mem (S : Subalgebra k (B P))
    (h01 : ∀ a, arrow01 P a ∈ S) (h12 : ∀ a, arrow12 P a ∈ S)
    (x : Paths k d) : pathMap P x ∈ S := by
  have hx := congrArg (pathMap P)
    ((RelationBasisCoefficients.pathBasis (k := k) (d := d)).sum_repr x)
  rw [map_sum] at hx
  rw [← hx]
  apply S.sum_mem
  intro ⟨b,a⟩ _
  rw [map_smul]
  apply S.smul_mem
  simp only [RelationBasisCoefficients.pathBasis, Module.Basis.tensorProduct_apply,
    Pi.basisFun_apply]
  change pathMap P (basis b ⊗ₜ[k] basis a) ∈ S
  rw [← arrow_product]
  exact S.mul_mem (h12 b) (h01 a)

/-- Vertices and the specified finite arrow list generate the full encoding,
including the quotient length-two path component. -/
theorem eq_top (S : Subalgebra k (B P))
    (hv : ∀ i, ThreeVertexAlgebra.vertex (composition P) i ∈ S)
    (h01 : ∀ a, arrow01 P a ∈ S) (h12 : ∀ a, arrow12 P a ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  rcases x with ⟨c0,c1,c2,v,w,z⟩
  obtain ⟨r,hr⟩ := Submodule.Quotient.mk_surjective (relationSpace P) z
  have hz : lengthTwo P z ∈ S := by
    rw [← hr]
    exact path_mem P S h01 h12 r
  have h := S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem
    (S.smul_mem (hv 0) c0) (S.smul_mem (hv 1) c1)) (S.smul_mem (hv 2) c2))
    (first_mem P S h01 v)) (second_mem P S h12 w)) hz
  simpa [ThreeVertexAlgebra.vertex, ThreeVertexAlgebra.add_eq,
    ThreeVertexAlgebra.smul_eq, first, second, lengthTwo] using h
end LittleFinitistic.EncodingGenerators

end

end OAI
