import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockLineGrid
import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundaryLocality

namespace OAI

/-! Carrier spread and Fourier separation at the actual source block windows. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace AngularGrid

/-- The neighbor radius at the final transition, in child-width units. -/
def sourceGap (g : AngularGrid) (L : ℝ) (child : ℕ) : ℝ :=
  SourceParameters.step L^(3/4:ℝ)*g.width child

theorem sourceGap_pos (g : AngularGrid) (L : ℝ) (child : ℕ) :
    0 < g.sourceGap L child :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos child)

/-- Both hypotheses of the separated-top count hold at the actual block
neighbor radius, including the initial shorter block. -/
theorem source_block_count_scales (g : AngularGrid) (L : ℝ) {B : ℝ}
    (hB : 0 < B) (base child : ℕ) (hblock : g.width base ≤ B*g.width child) :
    (g.rootWidth/B^2)/(g.branching:ℝ)^child ≤ g.sourceGap L child/B^2 ∧
      g.width base ≤ B*g.sourceGap L child := by
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hg : 1 ≤ SourceParameters.step L^(3/4:ℝ) := Real.one_le_rpow hG (by norm_num)
  have hw : g.width child ≤ g.sourceGap L child := by
    exact le_mul_of_one_le_left (g.width_pos child).le hg
  constructor
  · have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^child = g.width child/B^2 := by
      unfold width
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hw (sq_nonneg B)
  · exact hblock.trans (mul_le_mul_of_nonneg_left hw hB.le)

theorem centers_close_in_ancestor (g : AngularGrid) {base level : ℕ}
    (hle : base ≤ level) (s t : ℝ) (hcell : g.index base s = g.index base t) :
    |g.center level (g.index level s)-g.center level (g.index level t)| ≤
      2*g.width base := by
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have hst := g.same_cell_diameter base hcell
  have hw := g.width_antitone hle
  have htri : |g.center level (g.index level s)-g.center level (g.index level t)| ≤
      |s-g.center level (g.index level s)|+|s-t|+
        |t-g.center level (g.index level t)| := by
    calc
      _ = |(g.center level (g.index level s)-s)+(s-t)+
          (t-g.center level (g.index level t))| := by congr 1; ring
      _ ≤ |(g.center level (g.index level s)-s)+(s-t)|+
          |t-g.center level (g.index level t)| := abs_add_le _ _
      _ ≤ (|g.center level (g.index level s)-s|+|s-t|)+
          |t-g.center level (g.index level t)| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_sub_comm (g.center level (g.index level s)) s]
  linarith

/-- The full block length causes no loss in the carrier oscillation. -/
theorem source_block_carrier_mesh (g : AngularGrid) (L origin sR : ℝ)
    {w Cfreq eta : ℝ} (hw : 0 < w)
    (heta : |eta| ≤ Cfreq/w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (s t : ℝ) (hparent : g.index lower s = g.index lower t) :
    |(sR-g.center start (g.index start s))*eta-
      (sR-g.center start (g.index start t))*eta| *
      (sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
        (sourceLineScale_pos g L hw start)).meshWidth (start-lower) ≤
      (2*Cfreq)*SourceParameters.step L^(-(1/2:ℝ)) := by
  apply source_block_line_carrier g L origin hw lower start hle hbranch
  have hc := g.centers_close_in_ancestor hle s t hparent
  have heq : (sR-g.center start (g.index start s))*eta-
      (sR-g.center start (g.index start t))*eta =
      -(g.center start (g.index start s)-g.center start (g.index start t))*eta := by ring
  rw [heq,abs_mul,abs_neg]
  calc
    _ ≤ (2*g.width lower)*(Cfreq/w) :=
      mul_le_mul hc heta (abs_nonneg _) (mul_nonneg (by norm_num) (g.width_pos lower).le)
    _ = (2*Cfreq)*g.width lower/w := by ring

end AngularGrid

/-- Any fixed positive lower bound on transverse packet frequency suffices
for the source Fourier gap at all sufficiently large parameters. -/
theorem eventually_source_line_fourier_threshold {c0 : ℝ} (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop, ∀ (g : AngularGrid) (w : ℝ), 0 < w → ∀ level : ℕ,
      1/(sourceLineScale g L w level*SourceParameters.step L^(-(1/8:ℝ))) ≤
        (SourceParameters.step L^(3/4:ℝ)*g.width level)*(c0/w) := by
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually (gt_mem_nhds hc0)
  filter_upwards [hsmall] with L hL
  intro g w hw level
  exact source_line_fourier_threshold g L hw level hL.le

end LipschitzHilbert

end

end OAI
