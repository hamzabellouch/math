import OAI.MeasureTheory.Falconer.Estimates.CommonTubeKernel
import OAI.MeasureTheory.Falconer.Estimates.Packing

namespace OAI

/-! Separation supplies a second common-tube bound, independent of the
pencil cardinality. Interpolating it with regularity detects large pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem common_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l) :
    ((T.filter (fun l => TubeIncident δ y l)).card:ℝ) ≤
      (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  let S := T.filter fun l => TubeIncident δ y l
  by_cases hsmall : 16*δ ≤ r
  · have hrδ : δ < r := by linarith only [hδ,hsmall]
    have hxy : r ≤ dist x y := by
      have hh : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      exact (max_eq_right hh.le).trans_le (min_le_right _ _)
    by_cases hS : S.Nonempty
    · obtain ⟨m,hm⟩ := hS
      have hmT := (Finset.mem_filter.mp hm).1
      have hmy := (Finset.mem_filter.mp hm).2
      have hball : ∀ l ∈ S, dist l m ≤ 80*δ/r := by
        intro l hl
        obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
        exact two_point_tube_parameters_close hδ.le hr hr1 hsmall hx0
          (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy
      have hb := separated_ball_card S m hδ (by positivity : 0 ≤ 80*δ/r)
        (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hball
      have he : 2*(80*δ/r)/δ+1 = (160+r)/r := by field_simp; ring
      rw [he] at hb
      calc
        _ ≤ ((160+r)/r)^2 := hb
        _ ≤ (161/r)^2 := by gcongr; linarith only [hr1]
        _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring
    · change (S.card:ℝ) ≤ _
      rw [show S = ∅ from Finset.not_nonempty_iff_eq_empty.mp hS]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · have hball : ∀ l ∈ T, dist l 0 ≤ 2 := by
      intro l hl
      have hh := planar_dist_le_coordinate_sum l 0
      simp only [PiLp.zero_apply,sub_zero] at hh
      linarith only [hh,(hchart l hl).1,(hchart l hl).2]
    have hb := separated_ball_card T 0 hδ (by norm_num : (0:ℝ) ≤ 2) hsep hball
    have hratio : 4/δ+1 ≤ 80/r := by
      apply (le_div_iff₀ hr).2
      have hrδ : r ≤ 16*δ := (lt_of_not_ge hsmall).le
      have hrd : r/δ ≤ 16 := (div_le_iff₀ hδ).2 hrδ
      calc
        (4/δ+1)*r = 4*(r/δ)+r := by ring
        _ ≤ 4*16+1 := by gcongr
        _ ≤ 80 := by norm_num
    calc
      _ ≤ (T.card:ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ (4/δ+1)^2 := by norm_num only [show (2:ℝ)*2 = 4 by norm_num] at hb; exact hb
      _ ≤ (80/r)^2 := by gcongr
      _ ≤ (161/r)^2 := by gcongr; norm_num
      _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring

theorem intersect_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤ (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hl).1,hy l (Finset.mem_inter.mp hl).2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (common_tube_packing_bound hδ hδ1 T x y hx0 hchart hsep hx)

end Falconer

end OAI
