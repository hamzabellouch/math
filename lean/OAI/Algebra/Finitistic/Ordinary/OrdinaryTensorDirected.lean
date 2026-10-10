import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainDirected
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorDirected
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable {n : ℕ} (DB : DirectedBound.DirectedSystem k B 3) (DC : DirectedBound.DirectedSystem k C n)

def bIndex (i : Fin (n*3)) : Fin 3 := (finProdFinEquiv.symm i).2
def cIndex (i : Fin (n*3)) : Fin n := (finProdFinEquiv.symm i).1

theorem index_value (i : Fin (n*3)) : (bIndex i).val + 3 * (cIndex i).val = i.val :=
  congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)

def vertex (i : Fin (n*3)) : B ⊗[k] C := DB.e (bIndex i) ⊗ₜ[k] DC.e (cIndex i)

theorem vertex_idempotent (i : Fin (n*3)) : vertex DB DC i * vertex DB DC i = vertex DB DC i := by
  simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul,DB.idem,DC.idem]

theorem vertex_orthogonal (i j : Fin (n*3)) (hij : i ≠ j) : vertex DB DC i * vertex DB DC j = 0 := by
  simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hb : bIndex i = bIndex j
  · have hc : cIndex i ≠ cIndex j := by
      intro h
      apply hij
      apply Fin.ext
      have hi := index_value i
      have hj := index_value j
      rw [hb,h] at hi
      omega
    rw [DC.orthogonal _ _ hc,TensorProduct.tmul_zero]
  · rw [DB.orthogonal _ _ hb,TensorProduct.zero_tmul]

theorem vertex_complete : ∑ i : Fin (n*3), vertex DB DC i = 1 := by
  have h := Equiv.sum_comp (finProdFinEquiv : Fin n × Fin 3 ≃ Fin (n*3)) (vertex DB DC)
  rw [← h]
  simp only [vertex,bIndex,cIndex,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  have ht (x : Fin n) : (∑ j : Fin 3, DB.e j ⊗ₜ[k] DC.e x) = (1:B) ⊗ₜ[k] DC.e x := by
    rw [← TensorProduct.sum_tmul,DB.complete]
  simp_rw [ht]
  rw [← TensorProduct.tmul_sum,DC.complete]
  rfl

theorem vertex_diagonal (i : Fin (n*3)) (x : B ⊗[k] C) :
    ∃ r : k, vertex DB DC i * x * vertex DB DC i = r • vertex DB DC i := by
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    obtain ⟨r,hr⟩ := DB.diagonal (bIndex i) b
    obtain ⟨s,hs⟩ := DC.diagonal (cIndex i) c
    refine ⟨r*s,?_⟩
    simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul,hr,hs,
      TensorProduct.smul_tmul,TensorProduct.tmul_smul,smul_smul,mul_comm s r]
  | add x y hx hy =>
    obtain ⟨r,hr⟩ := hx
    obtain ⟨s,hs⟩ := hy
    exact ⟨r+s,by rw [mul_add,add_mul,hr,hs,add_smul]⟩

theorem vertex_directed (i j : Fin (n*3)) (hij : j < i) (x : B ⊗[k] C) :
    vertex DB DC j * x * vertex DB DC i = 0 := by
  have hi := index_value i
  have hj := index_value j
  have hbi := (bIndex i).isLt
  have hbj := (bIndex j).isLt
  change j.val < i.val at hij
  have hc : cIndex j < cIndex i ∨ (cIndex j = cIndex i ∧ bIndex j < bIndex i) := by
    by_cases h : cIndex j < cIndex i
    · exact Or.inl h
    · right
      have he : cIndex j = cIndex i := Fin.ext (by change ¬(cIndex j).val < (cIndex i).val at h; omega)
      exact ⟨he,by change (bIndex j).val < (bIndex i).val; rw [he] at hj; omega⟩
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul]
    rcases hc with h | ⟨h,hb⟩
    · rw [DC.directed _ _ h,TensorProduct.tmul_zero]
    · rw [DB.directed _ _ hb,TensorProduct.zero_tmul]
  | add x y hx hy => rw [mul_add,add_mul,hx,hy,add_zero]

/-- A concrete linear extension of the source's product order, with exactly 3n vertices. -/
def directedSystem : DirectedBound.DirectedSystem k (B ⊗[k] C) (n*3) where
  e := vertex DB DC
  idem := vertex_idempotent DB DC
  orthogonal := vertex_orthogonal DB DC
  complete := vertex_complete DB DC
  diagonal := vertex_diagonal DB DC
  directed := vertex_directed DB DC
end LittleFinitistic.OrdinarySimulation.TensorDirected

end

end OAI
