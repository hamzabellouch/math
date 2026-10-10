import OAI.Analysis.LienardCycles.CharacteristicJets

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates

noncomputable def RN (q : (ℝ × ℝ) × ℝ) : ℝ := 2*PN q+q.2*PNr q
noncomputable def GN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  PN q*(4*QN q+q.2*QNr q)-QN q*(2*PN q+q.2*PNr q)

lemma RN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω RN q := by
  unfold RN
  have h1 := PN_analytic q
  have h2 := PNr_analytic q
  fun_prop
lemma GN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω GN q := by
  unfold GN
  have h1 := PN_analytic q
  have h2 := PNr_analytic q
  have h3 := QN_analytic q
  have h4 := QNr_analytic q
  fun_prop
lemma RN_zero (d k : ℝ) : RN ((d,k),0)=2/3 := by
  norm_num [RN,PN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1)]
lemma GN_zero (d k : ℝ) : GN ((d,k),0)=2/45 := by
  norm_num [GN,PN,QN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),
    QuadraticVariation.Q_zero (by norm_num : (0:ℝ)<1)]
lemma G_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    G ((d,k),r)=r^5*GN ((d,k),r) := by
  dsimp [G]
  rw [R_scaled d k hr,S_scaled d k hr,P_scaling d k hr,Q_scaling d k hr]
  dsimp [GN,PN,QN]
  ring
lemma R_G_positive_near_zero (d k : ℝ) :
    ∀ᶠ q in 𝓝 ((d,k),(0:ℝ)), 0 < q.2 → 0 < R q ∧ 0 < G q := by
  have hp : 0 < RN ((d,k),0) := by rw [RN_zero]; norm_num
  have hq : 0 < GN ((d,k),0) := by rw [GN_zero]; norm_num
  filter_upwards [(RN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hp),
    (GN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hq)] with q h1 h2 hr
  rcases q with ⟨⟨d',k'⟩,r⟩
  constructor
  · rw [R_scaled d' k' hr]
    have hh := mul_pos hr h1
    dsimp [RN] at hh
    nlinarith only [hh]
  · rw [G_scaled d' k' hr]
    exact mul_pos (pow_pos hr 5) h2

end QuinticLienard.QuadraticCoordinates

end OAI
