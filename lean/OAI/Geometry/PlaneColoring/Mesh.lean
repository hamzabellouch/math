import OAI.Geometry.PlaneColoring.FullApproximation

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- A point of a connected set with a distant partner can be moved to the
boundary of its (unique) small hole. Pairwise disjoint closed disks make the
new point lie outside every open hole. No path regularity is required. -/
lemma connected_escape_holes {S : Finset MarkedDisk} {t : ℝ}
    (hS : ∀d∈S,0≤d.radius)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (hsum : (∑d∈S,d.radius)<t) {K : Set ℂ} (hK : IsPreconnected K)
    {a b : ℂ} (ha : a∈K) (hb : b∈K) (hab : 2*t<dist a b) :
    ∃a'∈K,a'∉diskHoles S ∧ dist a a'≤2*t := by
  have ht : 0<t := (Finset.sum_nonneg hS).trans_lt hsum
  by_cases haS : a∈diskHoles S
  · obtain ⟨d,hd,had⟩ := mem_diskHoles.mp haS
    have hrad : d.radius<t := (MarkedDisk.radius_le_sum hS hd).trans_lt hsum
    have had' : dist a d.center<d.radius := had
    have hbd : d.radius<dist b d.center := by
      by_contra! hh
      have htri := dist_triangle a d.center b
      rw [dist_comm d.center b] at htri
      linarith
    obtain ⟨p,hp,hpd⟩ := hK.intermediate_value ha hb
      (continuous_id.dist continuous_const).continuousOn ⟨had'.le,hbd.le⟩
    refine ⟨p,hp,MarkedDisk.sphere_avoids_holes hdis hd hpd,?_⟩
    change dist p d.center=d.radius at hpd
    have htri := dist_triangle a d.center p
    rw [dist_comm d.center p,hpd] at htri
    linarith
  · exact ⟨a,ha,haS,by simpa using (mul_pos (by norm_num : (0:ℝ)<2) ht).le⟩

/-- Positive averages on shrinking disks force every limit center into the
actual measure support of that color. -/
lemma support_of_positive_diskAverage_limit {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {a : ℕ → ℂ} {x : ℂ}
    (ha : Tendsto a atTop (𝓝 x)) (i : Fin k)
    (hp : ∀n,0<diskAverage c (ε n) i (a n)) : x∈spatialSupport c i := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hnear : ∀ᶠ n in atTop,dist (a n) x<r/2 := ha.eventually (Metric.ball_mem_nhds x (by positivity))
  have hsmall : ∀ᶠ n in atTop,ε n<r/2 := hε.eventually (gt_mem_nhds (by positivity : (0:ℝ)<r/2))
  obtain ⟨n,han,hεn⟩ := (hnear.and hsmall).exists
  have hsub : Metric.ball (a n) (ε n)⊆U := by
    intro z hz
    apply hrU
    have hh : dist z (a n)<ε n := hz
    have htri := dist_triangle z (a n) x
    change dist z x<r
    linarith
  have hpos := hp n
  rw [diskAverage_area hc] at hpos
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hzero' : volume (U∩{z | c z=i})=0 := by
    simpa only [spatialSupport,Measure.restrict_apply' (measurableSet_eq_fun hc measurable_const)] using hzero
  have hball : volume (Metric.ball (a n) (ε n)∩{z | c z=i})=0 :=
    measure_mono_null (inter_subset_inter_left _ hsub) hzero'
  simp only [Measure.real,hball,ENNReal.toReal_zero,zero_div,lt_self_iff_false] at hpos
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
namespace FullApprox
lemma ε_tendsto {c : ℂ → Fin 5} {α : ℝ} {t : ℕ → ℝ}
    (a : ∀n,FullApprox c α (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (a n).ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => (a n).ε_pos.le) (fun n => (a n).ε_lt.le) ht
lemma annuli_tendsto {c : ℂ → Fin 5} {α : ℝ} {t : ℕ → ℝ}
    (a : ∀n,FullApprox c α (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (a n).disks)) atTop (𝓝 0) := by
  apply holeAnnuli_tendsto_zero _ (fun n d hd => ((a n).positive d hd).le)
  exact squeeze_zero (fun n => Finset.sum_nonneg fun d hd => ((a n).positive d hd).le)
    (fun n => (a n).sum_lt.le) ht
lemma positive_average {c : ℂ → Fin 5} (hc : Measurable c) {α t : ℝ} (hα : α<1/5)
    (a : FullApprox c α t) (i : Fin 5) (q : Metric.closedBall (0:ℂ) 5)
    (hq : q.val∉diskHoles a.disks) (hp : 0<(a.map q).val i) : α<diskAverage c a.ε i q.val := by
  rw [a.agrees q hq] at hp
  exact (thresholdMap_pos hc a.ε_pos hα q.val i).mp hp

/-- A continuous graph approximant cannot have positive-coordinate connected
sets of macroscopic diameter at every shrinking scale. This is the manuscript
mesh argument, with connectedness replacing the stronger path assumption. -/
theorem no_large_positive_sequence {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {α : ℝ} (hα : 0<α) (hα' : α<1/5) {t : ℕ → ℝ}
    (F : ∀n,FullApprox c α (t n)) (htlim : Tendsto t atTop (𝓝 0))
    (htsmall : ∀n,t n≤1/16) (i : Fin 5)
    (hbad : ∀n,∃K : Set ℂ, IsPreconnected K ∧ K⊆Metric.closedBall (0:ℂ) 5 ∧
      (∀z : Metric.closedBall (0:ℂ) 5,z.val∈K → 0<((F n).map z).val i) ∧
      ∃x∈K,∃y∈K,2<dist x y) : False := by
  choose K hK hsub hprob x hx y hy hxy using hbad
  have hxy' (n : ℕ) : 2*t n<dist (x n) (y n) := by linarith [htsmall n,hxy n]
  have hyx' (n : ℕ) : 2*t n<dist (y n) (x n) := by rw [dist_comm]; exact hxy' n
  choose a haK haH hax using fun n => connected_escape_holes
    (fun d hd => ((F n).positive d hd).le) (F n).disjoint (F n).sum_lt (hK n) (hx n) (hy n) (hxy' n)
  choose b hbK hbH hby using fun n => connected_escape_holes
    (fun d hd => ((F n).positive d hd).le) (F n).disjoint (F n).sum_lt (hK n) (hy n) (hx n) (hyx' n)
  have hab (n : ℕ) : 3/2≤dist (a n) (b n) := by
    have h1 := dist_triangle (x n) (a n) (y n)
    have h2 := dist_triangle (a n) (b n) (y n)
    rw [dist_comm (b n) (y n)] at h2
    linarith [hxy n,hax n,hby n,htsmall n]
  obtain ⟨p,hp,φ,hφ,hlim⟩ := ((isCompact_closedBall (0:ℂ) 5).prod
    (isCompact_closedBall (0:ℂ) 5)).tendsto_subseq (x := fun n => (a n,b n)) (fun n => ⟨hsub n (haK n),hsub n (hbK n)⟩)
  have halim : Tendsto (fun n => a (φ n)) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
  have hblim : Tendsto (fun n => b (φ n)) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  have hpdist : 3/2≤dist p.1 p.2 := ge_of_tendsto (halim.dist hblim) (Eventually.of_forall (fun n => hab (φ n)))
  have hεlim := (ε_tendsto F htlim).comp hφ.tendsto_atTop
  have hE := (annuli_tendsto F htlim).comp hφ.tendsto_atTop
  have hasup : p.1∈spatialSupport c i := support_of_positive_diskAverage_limit hc hεlim halim i
    (fun n => hα.trans (positive_average hc hα' (F (φ n)) i ⟨a (φ n),hsub _ (haK _)⟩
      (haH _) (hprob _ _ (haK _))))
  have hexc : Disjoint (spatialSupport c i) (Metric.ball p.1 (1/8)) := by
    apply diskAverage_support_exclusion hc hεlim (fun n => (F (φ n)).ε_pos) hE hα Metric.isOpen_ball i
    intro z hz
    have hane : ∀ᶠn in atTop,dist (a (φ n)) p.1<1/8 :=
      halim.eventually (Metric.ball_mem_nhds _ (by norm_num))
    have hbne : ∀ᶠn in atTop,dist (b (φ n)) p.2<1/8 :=
      hblim.eventually (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [hane,hbne] with n han hbn hzE
    have hza : dist z (a (φ n))<1 := by
      have hh := dist_triangle z p.1 (a (φ n))
      rw [dist_comm p.1 (a (φ n))] at hh
      change dist z p.1<1/8 at hz
      linarith
    have hzb : 1<dist z (b (φ n)) := by
      have h1 := dist_triangle p.1 z p.2
      have h2 := dist_triangle z (b (φ n)) p.2
      rw [dist_comm p.1 z] at h1
      change dist z p.1<1/8 at hz
      linarith
    obtain ⟨q,hq,hunit⟩ := straddle_connected_unit (hK (φ n))
      ⟨a (φ n),haK _,b (φ n),hbK _,hza,hzb⟩
    have hqH : q∉diskHoles (F (φ n)).disks := fun hh => hzE (unit_from_hole_mem_annuli hh hunit)
    have hqprob := positive_average hc hα' (F (φ n)) i ⟨q,hsub _ hq⟩ hqH (hprob _ _ hq)
    have hu : ‖q-z‖=1 := by simpa only [dist_eq_norm,norm_sub_rev] using hunit
    have hh := diskAverage_unit_pair hc hw (F (φ n)).ε_pos hu i
    change diskAverage c (F (φ n)).ε i z≤1-α
    change α<diskAverage c (F (φ n)).ε i q at hqprob
    linarith
  exact Set.disjoint_left.mp hexc hasup (Metric.mem_ball_self (by norm_num))
end FullApprox
end EuclideanFiveColor
end

end OAI
