import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.Iterates

namespace OAI


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction Filter
open scoped CStarAlgebra ComplexOrder Topology

local instance matchingIteratedDecEq (n k : ℕ) : DecidableEq (IteratedIndex n k) :=
  diagIteratedDecEq n k

lemma continuous_finite_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (F : Finset C(Interval,CStarMatrix I I ℂ)) {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0,∀ f∈F,∀ s t : Interval,dist s t<δ → ‖f s-f t‖<ε := by
  classical
  let g : Interval → ({f // f∈F} → CStarMatrix I I ℂ) := fun t f => f.1 t
  have hg : Continuous g := continuous_pi (fun f => f.1.continuous)
  have hu := CompactSpace.uniformContinuous_of_continuous hg
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro f hf s t hst
  have hb := (dist_le_pi_dist (g s) (g t) ⟨f,hf⟩).trans_lt (hgδ hst)
  simpa only [g,dist_eq_norm] using hb

lemma unitary_conjugating_same_index {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (R : A →⋆ₐ[ℂ] B) (v w : unitary B) (x y : A) :
    ‖unitaryConjugation (w*v⁻¹) (unitaryConjugation v (R x))-
      unitaryConjugation w (R y)‖≤‖x-y‖ := by
  rw [←unitaryConjugation_mul]
  have hc : (w*v⁻¹)*v=w := by group
  rw [hc,←map_sub,←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation w) _).trans
    (NonUnitalStarAlgHom.norm_apply_le R _)

theorem stage_matching (n : ℕ) (F : Finset (Stage n)) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∃ W : C(Interval×Interval,
      unitary (TensorMat (pair (n+k)).p (pair (n+k)).q)),
      (∀ s : Interval,W (s,s)=1) ∧ ∀ f∈F,∀ s t : Interval,
        ‖unitaryConjugation (W (s,t)) ((system.map (Nat.le_add_right n k) f).val s)-
          (system.map (Nat.le_add_right n k) f).val t‖<ε := by
  classical
  obtain ⟨δ,hδ,hF⟩ := continuous_finite_uniform (F.image Subtype.val) hε
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨e,V,hV⟩ := iterate_diagonalization n k
  let R := (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom
  let W : C(Interval×Interval,unitary (TensorMat (pair (n+k)).p (pair (n+k)).q)) :=
    ⟨fun z => V z.2*(V z.1)⁻¹,by fun_prop⟩
  refine ⟨k,W,?_,?_⟩
  · intro s
    exact mul_inv_cancel (V s)
  · intro f hf s t
    rw [hV,hV]
    have hb : ‖blockDiagonalHom (fun j : IteratedIndex n k => f.val (iteratedFamily n k j s))-
        blockDiagonalHom (fun j : IteratedIndex n k => f.val (iteratedFamily n k j t))‖<ε := by
      rw [←map_sub]
      apply (NonUnitalStarAlgHom.norm_apply_le
        (blockDiagonalHom : (IteratedIndex n k → TensorMat (pair n).p (pair n).q) →⋆ₐ[ℂ]
          CStarMatrix ((Fin (pair n).p×Fin (pair n).q)×IteratedIndex n k)
            ((Fin (pair n).p×Fin (pair n).q)×IteratedIndex n k) ℂ) _).trans_lt
      apply (pi_norm_lt_iff hε).mpr
      intro j
      exact hF f.val (Finset.mem_image.mpr ⟨f,hf,rfl⟩) _ _
        ((iterated_variation n k j s t).trans_lt hk)
    have hc := unitary_conjugating_same_index R (V s) (V t)
      (blockDiagonalHom (fun j : IteratedIndex n k => f.val (iteratedFamily n k j s)))
      (blockDiagonalHom (fun j : IteratedIndex n k => f.val (iteratedFamily n k j t)))
    exact hc.trans_lt hb

end OriginalJiangSu

end

end OAI
