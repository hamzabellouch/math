import OAI.MeasureTheory.Falconer.Estimates.PointSamples
import OAI.MeasureTheory.Falconer.Geometry.PlanarScalarGrid

namespace OAI

/-! Fixed finite losses for the nearby grid images of the tube packet.
The factor 361 is the planar packing bound in a ball of radius nine mesh
lengths. Both directions of the cardinality comparison will be needed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem separated_near_cover_card {δ : ℝ} (hδ : 0 < δ)
    (S V : Finset (Space 2)) (hsep : FiniteSeparatedAt δ S)
    (hcover : ∀ x ∈ S, ∃ y ∈ V, dist x y ≤ 9*δ) :
    (S.card:ℝ) ≤ 361*(V.card:ℝ) := by
  have hcount (y : Space 2) (_hy : y ∈ V) :
      ((S.filter fun x => dist x y ≤ 9*δ).card:ℝ) ≤ 361 := by
    have hh := separated_ball_card (S.filter fun x => dist x y ≤ 9*δ) y hδ
      (show 0 ≤ 9*δ by positivity)
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z
        (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have he : 2*(9*δ)/δ+1 = (19:ℝ) := by field_simp; ring
    norm_num only [he, Nat.cast_ofNat, Nat.reducePow] at hh
    exact hh
  have hh := selected_points_card_lower S id V hcover hcount
  simpa only [id_eq,mul_comm] using hh

theorem nearby_image_card {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Space 2)) (f : Space 2 → Space 2)
    (hsep : FiniteSeparatedAt δ S) (hnear : ∀ x ∈ S, dist x (f x) ≤ 9*δ) :
    (S.card:ℝ) ≤ 361*((S.image f).card:ℝ) :=
  separated_near_cover_card hδ S (S.image f) hsep
    (fun x hx => ⟨f x,Finset.mem_image_of_mem f hx,hnear x hx⟩)

theorem nearby_image_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (S : Finset (Space 2)) (f : Space 2 → Space 2)
    (hsep : FiniteSeparatedAt δ S) (hnear : ∀ x ∈ S, dist x (f x) ≤ 9*δ)
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound δ s (361*K*(10:ℝ)^s) (S.image f) := by
  intro z r hr _
  have hr0 : 0 < r := hδ.trans_le hr
  have hsub : (S.image f).filter (fun y => dist y z ≤ r) ⊆
      (S.filter (fun x => dist x z ≤ 10*r)).image f := by
    intro y hy
    obtain ⟨hy,hyr⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := (dist_triangle x (f x) z).trans (add_le_add (hnear x hx) hyr)
    linarith only [hh,hr]
  have hsize := nearby_image_card hδ S f hsep hnear
  calc
    _ ≤ ((S.filter fun x => dist x z ≤ 10*r).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(10*r)^s*(S.card:ℝ) :=
      normalized_ball_bound_all_radii hs hK hreg z (10*r) (by linarith only [hr,hδ])
    _ ≤ K*(10*r)^s*(361*((S.image f).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) hr0.le]; ring

end Falconer

end OAI
