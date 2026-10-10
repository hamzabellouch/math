import OAI.MeasureTheory.Falconer.Geometry.PlanarProjectionCoordinates

namespace OAI

/-! Exact inverse coordinates and ball-count transport for the two
separated projections selected from the original planar configuration. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarProjectionInverse (a b : ℝ) (z : Space 2) : Space 2 :=
  rowPoint ((z 1-z 0)/(b-a)) ((b*z 0-a*z 1)/(b-a))

 theorem planarProjectionCoordinates_right_inverse {a b : ℝ} (hab : b ≠ a) (z : Space 2) :
    planarProjectionCoordinates a b (planarProjectionInverse a b z) = z := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  ext i
  fin_cases i
  · change a*((z 1-z 0)/(b-a))+(b*z 0-a*z 1)/(b-a) = z 0
    field_simp
    ring
  · change b*((z 1-z 0)/(b-a))+(b*z 0-a*z 1)/(b-a) = z 1
    field_simp
    ring

 theorem planarProjectionCoordinates_left_inverse {a b : ℝ} (hab : b ≠ a) (l : Space 2) :
    planarProjectionInverse a b (planarProjectionCoordinates a b l) = l := by
  apply planarProjectionCoordinates_injective hab
  exact planarProjectionCoordinates_right_inverse hab _

 theorem planarProjectionCoordinates_separated {δ a b : ℝ} (_hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/(4/|b-a|)) (G.image (planarProjectionCoordinates a b)) := by
  intro x hx y hy hne
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hy
  have hlm : l ≠ m := fun h => hne (congrArg (planarProjectionCoordinates a b) h)
  have hL : 0 < 4/|b-a| := div_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hab))
  apply (div_le_iff₀ hL).2
  exact (hsep l hl m hm hlm).trans (by
    simpa only [mul_comm] using planarProjectionCoordinates_dist_lower hab ha hb l m)

 theorem planarProjectionCoordinates_regular {δ t K a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/(4/|b-a|)) t (K*(4/|b-a|)^t)
      (G.image (planarProjectionCoordinates a b)) := by
  classical
  let f := planarProjectionCoordinates a b
  let L := 4/|b-a|
  have hL : 0 < L := div_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hab))
  have hcard : (G.image f).card = G.card :=
    Finset.card_image_of_injective G (planarProjectionCoordinates_injective hab)
  intro z r hr _
  have hr0 : 0 < r := (div_pos hδ hL).trans_le hr
  have hdr : δ ≤ L*r := by
    have hh := (div_le_iff₀ hL).1 hr
    nlinarith
  let u := planarProjectionInverse a b z
  have hfu : f u = z := planarProjectionCoordinates_right_inverse hab z
  have hsub : (G.image f).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun l => dist l u ≤ L*r)).image f := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,?_⟩,rfl⟩
    have hh := planarProjectionCoordinates_dist_lower hab ha hb l u
    change dist l u ≤ L*dist (f l) (f u) at hh
    rw [hfu] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpr hL.le)
  have hc : (((G.image f).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun l => dist l u ≤ L*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hball := normalized_ball_bound_all_radii ht hK hreg u (L*r) hdr
  rw [Real.mul_rpow hL.le hr0.le] at hball
  change (((G.image f).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
    K*L^t*r^t*((G.image f).card:ℝ)
  rw [hcard]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
