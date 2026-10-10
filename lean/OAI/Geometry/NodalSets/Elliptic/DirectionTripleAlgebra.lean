import OAI.Geometry.NodalSets.Elliptic.LocalDirection

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def transverseTriple (eps : ℝ) : Fin 3 → Coord :=
  ![Pi.single 1 1, Pi.single 1 1 + eps • Pi.single 2 1,
    Pi.single 1 1 + eps • Pi.single 3 1]

lemma transverseTriple_ne_zero (eps : ℝ) (j : Fin 3) : transverseTriple eps j ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Coord ↦ v 1) h
  fin_cases j <;> simp [transverseTriple] at h1

lemma transverseTriple_independent (eps : ℝ) (heps : eps ≠ 0) :
    LinearIndependent ℝ (transverseTriple eps) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (fun v : Coord ↦ v 1) hc
  have h2 := congrArg (fun v : Coord ↦ v 2) hc
  have h3 := congrArg (fun v : Coord ↦ v 3) hc
  simp [Fin.sum_univ_succ,transverseTriple] at h1 h2 h3
  have hc1 : c 1 = 0 := h2.resolve_right heps
  have hc2 : c 2 = 0 := h3.resolve_right heps
  have hc0 : c 0 = 0 := by simpa [hc1,hc2] using h1
  fin_cases j <;> assumption

lemma rescaled_frame_triple_independent (e : Coord ≃L[ℝ] Coord)
    (eps : ℝ) (heps : eps ≠ 0) (a : Fin 3 → ℝ) (ha : ∀ j, a j ≠ 0) :
    LinearIndependent ℝ (fun j ↦ a j • e (transverseTriple eps j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have he := congrArg e.symm hc
  simp only [map_sum,map_smul,ContinuousLinearEquiv.symm_apply_apply,map_zero,smul_smul] at he
  have h := Fintype.linearIndependent_iff.mp (transverseTriple_independent eps heps)
    (fun i ↦ c i*a i) he j
  exact (mul_eq_zero.mp h).resolve_right (ha j)

lemma transverseTriple_representation (eps : ℝ) (heps : eps ≠ 0) (v : Coord) (hv : v 0 = 0) :
    v = (v 1-v 2/eps-v 3/eps) • transverseTriple eps 0 +
      (v 2/eps) • transverseTriple eps 1 + (v 3/eps) • transverseTriple eps 2 := by
  ext i
  fin_cases i <;> simp [transverseTriple,hv] <;> field_simp
  ring

lemma rescaled_frame_triple_spans (e : Coord ≃L[ℝ] Coord)
    (eps : ℝ) (heps : eps ≠ 0) (a : Fin 3 → ℝ) (ha : ∀ j, a j ≠ 0)
    (v : Coord) (hv : e.symm v 0 = 0) :
    v ∈ Submodule.span ℝ (Set.range (fun j ↦ a j • e (transverseTriple eps j))) := by
  let P := Submodule.span ℝ (Set.range (fun j ↦ a j • e (transverseTriple eps j)))
  have hm (j : Fin 3) : e (transverseTriple eps j) ∈ P := by
    have h := P.smul_mem (a j)⁻¹ (Submodule.subset_span (Set.mem_range_self j))
    simpa [smul_smul,ha j] using h
  have he := congrArg e (transverseTriple_representation eps heps (e.symm v) hv)
  simp only [map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply] at he
  rw [he]
  exact P.add_mem (P.add_mem (P.smul_mem _ (hm 0)) (P.smul_mem _ (hm 1))) (P.smul_mem _ (hm 2))

end
end Yau.Geometry

end OAI
