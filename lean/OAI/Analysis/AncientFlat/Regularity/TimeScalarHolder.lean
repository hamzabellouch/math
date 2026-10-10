import OAI.Analysis.AncientFlat.Regularity.HolderTimeChange

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff NNReal
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma time_smooth_holder [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (J : Set ℝ) (hJ : IsCompact J) (hJc : Convex ℝ J)
    (f : ℝ → E) (hf : ContDiffOn ℝ 1 f J) :
    ∃ C : ℝ, 0<C ∧ HolderBound α {p : V × ℝ | p.2∈J} (fun p => f p.2) C := by
  obtain ⟨B0,hB0⟩ := hJ.exists_bound_of_continuousOn hf.continuousOn
  let B := max B0 0
  have hB : 0≤B := le_max_right _ _
  have hBb (t) (ht : t∈J) : ‖f t‖≤B := (hB0 t ht).trans (le_max_left _ _)
  obtain ⟨L,hL⟩ := hf.exists_lipschitzOnWith (by norm_num) hJc hJ
  refine ⟨2*B+L+1,by positivity,?_,?_⟩
  · intro p hp
    exact (hBb _ hp).trans (by linarith [L.coe_nonneg])
  · intro p hp q hq
    by_cases hd : pdist p q≤1
    · have ht : ‖p.2-q.2‖≤pdist p q :=
        (norm_snd_le (p-q)).trans (ParabolicLocalization.norm_pair_sub_le_pdist p q hd)
      calc
        _ ≤ (L:ℝ)*‖p.2-q.2‖ := hL.norm_sub_le hp hq
        _ ≤ (L:ℝ)*pdist p q := mul_le_mul_of_nonneg_left ht L.coe_nonneg
        _ ≤ (L:ℝ)*pdist p q^α := mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one (pdist_nonneg _ _) hd hα1) L.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [L.coe_nonneg]) (Real.rpow_nonneg (pdist_nonneg _ _) _)
    · have hh : 1≤pdist p q^α := Real.one_le_rpow (le_of_not_ge hd) hα.le
      calc
        _ ≤ ‖f p.2‖+‖f q.2‖ := norm_sub_le _ _
        _ ≤ 2*B := by linarith [hBb _ hp,hBb _ hq]
        _ ≤ (2*B+L+1)*pdist p q^α := by nlinarith [L.coe_nonneg]
end ParabolicInterior

end

end OAI
