import OAI.MeasureTheory.Falconer.Radial.AffineSubspaceFrostman
import OAI.MeasureTheory.Falconer.Angular.AngularTubes

namespace OAI

/-! # The codimension-two plane orthogonal to two orthonormal directions -/

namespace Falconer
open Set Submodule
open scoped BigOperators
variable {d : ℕ}

theorem orthonormal_pair_complement (v : Fin 2 → Space d) (hv : Orthonormal ℝ v) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∀ z : Space d, ‖Vᗮ.starProjection z‖ ≤ |inner ℝ (v 0) z|+|inner ℝ (v 1) z| := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  refine ⟨Wᗮ,?_,?_⟩
  · have hdim : Module.finrank ℝ W = 2 := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hv.linearIndependent
    have hd := W.finrank_add_finrank_orthogonal
    rw [hdim] at hd
    simp only [finrank_euclideanSpace_fin] at hd
    omega
  · intro z
    let p := ∑ i : Fin 2, inner ℝ (v i) z • v i
    have hp : p ∈ W := Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    have hpinner (i : Fin 2) : inner ℝ p (v i) = inner ℝ z (v i) := by
      calc
        _ = inner ℝ (v i) p := real_inner_comm _ _
        _ = inner ℝ (v i) z := hv.inner_right_fintype (fun j => inner ℝ (v j) z) i
        _ = _ := real_inner_comm _ _
    have he : W.starProjection z = p := by
      apply W.eq_starProjection_of_mem_of_inner_eq_zero hp
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i,rfl⟩ := hw
        rw [inner_sub_left,hpinner,sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp only [inner_add_right,hx,hy,add_zero]
      | smul a x _ hx => simp only [inner_smul_right,hx,mul_zero]
    simp only [Submodule.orthogonal_orthogonal]
    rw [he]
    calc
      _ ≤ ∑ i : Fin 2, ‖inner ℝ (v i) z • v i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul,hv.norm_eq_one,Fin.sum_univ_two]

end Falconer

end OAI
