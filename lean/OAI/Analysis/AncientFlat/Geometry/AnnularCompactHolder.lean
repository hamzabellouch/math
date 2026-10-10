import OAI.Analysis.AncientFlat.Profile.CompactificationDerivative

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
open ParabolicInterior
def rectangle : Set (ℝ × ℝ) := Icc (1/2) 2 ×ˢ Icc 0 4
lemma rectangle_compact : IsCompact rectangle := isCompact_Icc.prod isCompact_Icc
lemma rectangle_convex : Convex ℝ rectangle := (convex_Icc _ _).prod (convex_Icc _ _)
variable {V : Type} [NormedAddCommGroup V]
lemma outer_to_rectangle {p : V × ℝ} (hp : p∈outer) : (‖p.1‖,-p.2)∈rectangle := by
  rcases hp with ⟨h1,h2,h3,h4⟩
  exact ⟨⟨h1.le,h2.le⟩,⟨by linarith,by linarith⟩⟩
lemma norm_radial_pair_le {p q : V × ℝ} (hd : pdist p q≤1) :
    ‖(‖p.1‖,-p.2)-(‖q.1‖,-q.2)‖≤pdist p q := by
  have ht : |p.2-q.2|≤1 := by
    by_contra hn
    have hr : 1 < |p.2-q.2| ^((1:ℝ)/4) := Real.one_lt_rpow (lt_of_not_ge hn) (by norm_num)
    dsimp [pdist] at hd
    linarith [norm_nonneg (p.1-q.1)]
  apply norm_prod_le_iff.mpr
  constructor
  · change |‖p.1‖-‖q.1‖|≤_
    exact (abs_norm_sub_norm_le _ _).trans (by dsimp [pdist]; exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  · change |-p.2-(-q.2)|≤_
    rw [show -p.2-(-q.2)=-(p.2-q.2) by ring,abs_neg]
    exact (Real.self_le_rpow_of_le_one (abs_nonneg _) ht (by norm_num : (1:ℝ)/4≤1)).trans
      (by dsimp [pdist]; linarith [norm_nonneg (p.1-q.1)])
lemma compact_radial_holder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (hα : 0<α) (hα1 : α≤1) (m : ℝ × ℝ → E)
    (hm : ContDiffOn ℝ 1 m rectangle) :
    ∃ K : ℝ, 0<K ∧ HolderBound α outer (fun p : V × ℝ => m (‖p.1‖,-p.2)) K := by
  obtain ⟨B0,hB0⟩ := rectangle_compact.exists_bound_of_continuousOn hm.continuousOn
  let B := max B0 0
  have hB : 0≤B := le_max_right _ _
  have hBb (z) (hz : z∈rectangle) : ‖m z‖≤B := (hB0 z hz).trans (le_max_left _ _)
  obtain ⟨L,hL⟩ := hm.exists_lipschitzOnWith (by norm_num) rectangle_convex rectangle_compact
  refine ⟨2*B+L+1,by positivity,?_,?_⟩
  · intro p hp
    exact (hBb _ (outer_to_rectangle hp)).trans (by linarith [L.coe_nonneg])
  · intro p hp q hq
    by_cases hd : pdist p q≤1
    · calc
        _ ≤ (L:ℝ)*‖(‖p.1‖,-p.2)-(‖q.1‖,-q.2)‖ :=
          hL.norm_sub_le (outer_to_rectangle hp) (outer_to_rectangle hq)
        _ ≤ (L:ℝ)*pdist p q := mul_le_mul_of_nonneg_left (norm_radial_pair_le hd) L.coe_nonneg
        _ ≤ (L:ℝ)*pdist p q^α := mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one (pdist_nonneg _ _) hd hα1) L.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [L.coe_nonneg]) (Real.rpow_nonneg (pdist_nonneg _ _) _)
    · have hh : 1≤pdist p q^α := Real.one_le_rpow (le_of_not_ge hd) hα.le
      calc
        _ ≤ ‖m (‖p.1‖,-p.2)‖+‖m (‖q.1‖,-q.2)‖ := norm_sub_le _ _
        _ ≤ 2*B := by linarith [hBb _ (outer_to_rectangle hp),hBb _ (outer_to_rectangle hq)]
        _ ≤ (2*B+L+1)*pdist p q^α := by nlinarith [L.coe_nonneg]
end ParabolicAnnular

end

end OAI
