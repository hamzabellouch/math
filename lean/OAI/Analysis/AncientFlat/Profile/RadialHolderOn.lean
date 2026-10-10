import OAI.Analysis.AncientFlat.Geometry.AnnularCompactHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
lemma compact_radial_holder_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (hα : 0<α) (hα1 : α≤1) (m : ℝ × ℝ → E)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hm : ContDiffOn ℝ 1 m K) (Ω : Set (V × ℝ))
    (hmap : ∀ p∈Ω, (‖p.1‖,-p.2)∈K) :
    ∃ C : ℝ, 0<C ∧ HolderBound α Ω (fun p : V × ℝ => m (‖p.1‖,-p.2)) C := by
  obtain ⟨B0,hB0⟩ := hK.exists_bound_of_continuousOn hm.continuousOn
  let B := max B0 0
  have hB : 0≤B := le_max_right _ _
  have hBb (z) (hz : z∈K) : ‖m z‖≤B := (hB0 z hz).trans (le_max_left _ _)
  obtain ⟨L,hL⟩ := hm.exists_lipschitzOnWith (by norm_num) hKc hK
  refine ⟨2*B+L+1,by positivity,?_,?_⟩
  · intro p hp
    exact (hBb _ (hmap p hp)).trans (by linarith [L.coe_nonneg])
  · intro p hp q hq
    by_cases hd : pdist p q≤1
    · calc
        _ ≤ (L:ℝ)*‖(‖p.1‖,-p.2)-(‖q.1‖,-q.2)‖ := hL.norm_sub_le (hmap p hp) (hmap q hq)
        _ ≤ (L:ℝ)*pdist p q := mul_le_mul_of_nonneg_left (norm_radial_pair_le hd) L.coe_nonneg
        _ ≤ (L:ℝ)*pdist p q^α := mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one (pdist_nonneg _ _) hd hα1) L.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [L.coe_nonneg]) (Real.rpow_nonneg (pdist_nonneg _ _) _)
    · have hh : 1≤pdist p q^α := Real.one_le_rpow (le_of_not_ge hd) hα.le
      calc
        _ ≤ ‖m (‖p.1‖,-p.2)‖+‖m (‖q.1‖,-q.2)‖ := norm_sub_le _ _
        _ ≤ 2*B := by linarith [hBb _ (hmap p hp),hBb _ (hmap q hq)]
        _ ≤ (2*B+L+1)*pdist p q^α := by nlinarith [L.coe_nonneg]
end ParabolicAnnular

end

end OAI
