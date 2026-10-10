import OAI.MeasureTheory.Falconer.Estimates.PlanarQuarter
import OAI.MeasureTheory.Falconer.Estimates.LocalCellLines

namespace OAI

/-! A fixed point contraction and its exact line map. This preserves the
original incidence witnesses and the dyadic scale needed by regular gain. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem unlocalCellLine_four_dist (l m : Space 2) :
    dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m) ≤ 4*dist l m := by
  have h := EuclideanSpace.dist_sq_eq l m
  have h' := EuclideanSpace.dist_sq_eq (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h h'
  change dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)^2 =
    (l 0-m 0)^2+((4*l 1-l 0*0+0)-(4*m 1-m 0*0+0))^2 at h'
  nlinarith [sq_nonneg (l 0-m 0),dist_nonneg (x := l) (y := m),
    dist_nonneg (x := unlocalCellLine 4 0 0 l) (y := unlocalCellLine 4 0 0 m)]

theorem localCellLine_four_separated {δ : ℝ} (T : Finset (Space 2))
    (hT : FiniteSeparatedAt δ T) :
    FiniteSeparatedAt (δ/4) (T.image (localCellLine 4 0 0)) := by
  intro l hl m hm hlm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hm
  have hsep := hT a ha b hb (fun he => hlm (congrArg (localCellLine 4 0 0) he))
  have hd := unlocalCellLine_four_dist (localCellLine 4 0 0 a) (localCellLine 4 0 0 b)
  rw [localCellLine_leftInverse (by norm_num) 0 0 a,
    localCellLine_leftInverse (by norm_num) 0 0 b] at hd
  linarith

theorem localCellLine_four_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (T : Finset (Space 2))
    (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound (δ/4) s (K*4^s) (T.image (localCellLine 4 0 0)) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  let w := unlocalCellLine 4 0 0 z
  have hsub : (T.image (localCellLine 4 0 0)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 4*r)).image (localCellLine 4 0 0) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,rfl⟩
    have hh := unlocalCellLine_four_dist (localCellLine 4 0 0 a) z
    rw [localCellLine_leftInverse (by norm_num) 0 0 a] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 4*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(4*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (4*r)
      (by linarith only [hr])
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem planarQuarter_eq_local (p : Space 2) : planarQuarter p = localPacketPoint 4 0 0 p := by
  ext i
  fin_cases i <;> simp [planarQuarter_apply,localPacketPoint]

theorem planarQuarter_incident {δ : ℝ} {p l : Space 2} (h : TubeIncident δ p l) :
    TubeIncident (δ/4) (planarQuarter p) (localCellLine 4 0 0 l) := by
  rw [planarQuarter_eq_local]
  exact localCellLine_incident (by norm_num) 0 0 p l h

theorem localCellLine_four_chart (T : Finset (Space 2)) (hT : InBoundedLineChart T) :
    InBoundedLineChart (T.image (localCellLine 4 0 0)) := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  constructor
  · exact (hT a ha).1
  · change |(a 0*0+a 1-0)/(4:ℝ)| ≤ 1
    rw [abs_div]
    norm_num only [mul_zero,zero_add,sub_zero,abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith only [(hT a ha).2]

end Falconer

end OAI
