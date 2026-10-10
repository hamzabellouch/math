import OAI.Probability.SpanningForest.ReducedLaplacian
import OAI.Probability.SpanningForest.IncidenceUnimodular
import OAI.Probability.SpanningForest.DisconnectedIncidence
import OAI.Probability.SpanningForest.WeightedCauchyBinet

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.IncidenceMinor

open ReducedLaplacian Classical

variable {V E : Type*}

theorem connected_iff_root_reachable (src dst : E → V) (root : V) :
    Connected src dst ↔
      ∀ v, Relation.ReflTransGen (EdgeAdj src dst) root v := by
  constructor
  · intro h v
    exact h root v
  · intro h
    let : Std.Symm (EdgeAdj src dst) := ⟨fun _ _ ⟨e, he⟩ => ⟨e, he.symm⟩⟩
    intro u v
    exact (symm (h u)).trans (h v)

variable [Fintype V] [DecidableEq V]

theorem reducedGradient_det_ne_zero (root : V)
    (src dst : {v : V // v ≠ root} → V) (hconn : Connected src dst) :
    (reducedGradient src dst root).det ≠ 0 := by
  have hu : IsUnit (reducedGradient src dst root) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (reducedGradient_mulVec_injective src dst root hconn)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

theorem reducedGradient_det_eq_zero (root : V)
    (src dst : {v : V // v ≠ root} → V) (hconn : ¬Connected src dst) :
    (reducedGradient src dst root).det = 0 := by
  have hroot : ¬∀ v, Relation.ReflTransGen (EdgeAdj src dst) root v :=
    fun h => hconn ((connected_iff_root_reachable src dst root).mpr h)
  change ((IncidenceDisconnected.reducedIncidence root src dst)ᵀ).det = 0
  rw [Matrix.det_transpose]
  exact IncidenceDisconnected.det_reducedIncidence_eq_zero_of_not_connected
    root src dst hroot

theorem reducedGradient_det_ne_zero_iff (root : V)
    (src dst : {v : V // v ≠ root} → V) :
    (reducedGradient src dst root).det ≠ 0 ↔ Connected src dst := by
  constructor
  · intro hd
    by_contra hc
    exact hd (reducedGradient_det_eq_zero root src dst hc)
  · exact reducedGradient_det_ne_zero root src dst

theorem reducedGradient_det_sq_eq_indicator (root : V)
    (src dst : {v : V // v ≠ root} → V) :
    (reducedGradient src dst root).det ^ 2 =
      if Connected src dst then 1 else 0 := by
  classical
  by_cases hc : Connected src dst
  · rw [ite_eq_left hc]
    have hd := reducedGradient_det_ne_zero root src dst hc
    have hs := Incidence.signedIncidence_det_sq_eq_one_of_ne_zero
      src dst (fun v : {v : V // v ≠ root} => v.val) id
      (by
        change ((reducedGradient src dst root)ᵀ).det ≠ 0
        simpa only [Matrix.det_transpose] using hd)
    change ((reducedGradient src dst root)ᵀ).det ^ 2 = 1 at hs
    simpa only [Matrix.det_transpose] using hs
  · rw [ite_eq_right hc, reducedGradient_det_eq_zero root src dst hc]
    norm_num

theorem selected_minor_det_sq_eq_indicator (src dst : E → V) (root : V)
    (f : {v : V // v ≠ root} → E) :
    (((reducedGradient src dst root)ᵀ).submatrix id f).det ^ 2 =
      if Connected (src ∘ f) (dst ∘ f) then 1 else 0 := by
  have heq : ((reducedGradient src dst root)ᵀ).submatrix id f =
      (reducedGradient (src ∘ f) (dst ∘ f) root)ᵀ := rfl
  rw [heq, Matrix.det_transpose, reducedGradient_det_sq_eq_indicator]

theorem weightedLaplacian_connected_list_partition [Fintype E] [DecidableEq E]
    (src dst : E → V) (root : V) (c : E → ℝ) :
    (weightedLaplacian src dst root c).det =
      (∑ f : {v : V // v ≠ root} → E,
        if Connected (src ∘ f) (dst ∘ f) then ∏ i, c (f i) else 0) /
          (Fintype.card {v : V // v ≠ root}).factorial := by
  have h := WeightedCauchyBinet.weighted_gram_det_real
    (reducedGradient src dst root)ᵀ c
  simp only [Matrix.transpose_transpose] at h
  rw [weightedLaplacian, h]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  rw [selected_minor_det_sq_eq_indicator]
  split_ifs <;> simp

end Problem336.IncidenceMinor

end

end OAI
