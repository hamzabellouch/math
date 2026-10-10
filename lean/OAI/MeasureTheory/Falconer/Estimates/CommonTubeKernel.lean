import OAI.MeasureTheory.Falconer.Incidence.CommonTubeCount

namespace OAI

/-! A common-tube kernel valid at all point separations, including the diagonal. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

noncomputable def truncatedPlanarDistance (δ : ℝ) (x y : Space 2) : ℝ :=
  max δ (min 1 (dist x y))

theorem truncatedPlanarDistance_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x y : Space 2) :
    0 < truncatedPlanarDistance δ x y ∧ truncatedPlanarDistance δ x y ≤ 1 :=
  ⟨hδ.trans_le (le_max_left _ _),max_le hδ1 (min_le_left _ _)⟩

theorem common_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  by_cases hsmall : 80*δ ≤ r
  · have hlow : 16*δ ≤ r := by linarith
    have hR : 80*δ/r ≤ 1 := (div_le_one hr).2 hsmall
    have hrδ : δ < r := by linarith
    have hdist : r ≤ dist x y := by
      have hm : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      change max δ (min 1 (dist x y)) ≤ dist x y
      rw [max_eq_right hm.le]
      exact min_le_right _ _
    exact common_tube_card_bound hδ hr hr1 hlow hR (zero_le_one.trans hK)
      T x y hx0 hdist hchart hinc hball
  · have hR : 1 ≤ 80*δ/r := (le_div_iff₀ hr).2 (by linarith)
    have hp : 1 ≤ (80*δ/r)^b := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hR hb
    have hm : 1 ≤ K*(80*δ/r)^b := by nlinarith
    calc
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_filter_le T _
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) T.card]

theorem intersect_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤ K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    obtain ⟨hlT,hlU⟩ := Finset.mem_inter.mp hl
    exact Finset.mem_filter.mpr ⟨hlT,hy l hlU⟩
  exact (show ((T ∩ U).card : ℝ) ≤ (T.filter (fun l => TubeIncident δ y l)).card by
    exact_mod_cast Finset.card_le_card hsub).trans
      (common_tube_kernel_bound hδ hδ1 hb hK T x y hx0 hchart hx hball)

end Falconer

end OAI
