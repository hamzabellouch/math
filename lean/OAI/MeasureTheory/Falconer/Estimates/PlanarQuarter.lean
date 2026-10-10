import OAI.MeasureTheory.Falconer.Geometry.ProjectionCoordinateBalls

namespace OAI

/-! A fixed contraction puts the actual two projection coordinates inside
one bounded square without changing their finite combinatorics. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarQuarter (p : Space 2) : Space 2 := (1/4:ℝ) • p

 theorem planarQuarter_apply (p : Space 2) (i : Fin 2) : planarQuarter p i = p i / 4 := by
  change (1/4:ℝ) * p i = p i / 4
  ring

 theorem planarQuarter_dist (p q : Space 2) :
    dist (planarQuarter p) (planarQuarter q) = dist p q / 4 := by
  rw [planarQuarter,planarQuarter,dist_smul₀]
  norm_num
  ring

 theorem planarQuarter_injective : Function.Injective planarQuarter := by
  intro p q h
  have hh : dist p q / 4 = 0 := by rw [← planarQuarter_dist,h,dist_self]
  exact dist_eq_zero.mp (by linarith)

 theorem planarQuarter_right_inverse (z : Space 2) : planarQuarter ((4:ℝ) • z) = z := by
  ext i
  rw [planarQuarter_apply]
  change 4 * z i / 4 = z i
  ring

 theorem planarQuarter_separated {δ : ℝ} (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/4) (G.image planarQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  rw [planarQuarter_dist]
  exact div_le_div_of_nonneg_right (hsep x hx y hy (fun h => hpq (congrArg _ h))) (by norm_num)

 theorem planarQuarter_regular {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/4) t (K*4^t) (G.image planarQuarter) := by
  classical
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (G.image planarQuarter).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).image planarQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := planarQuarter_dist x ((4:ℝ) • z)
    rw [planarQuarter_right_inverse] at hh
    linarith
  have hc : (((G.image planarQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg ((4:ℝ) • z) (4*r) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le] at hb
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
