import OAI.Geometry.PlaneColoring.DiskExtension

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma radius_le_sum {S : Finset MarkedDisk} (hS : ∀d∈S,0≤d.radius) {d : MarkedDisk} (hd : d∈S) :
    d.radius≤∑e∈S,e.radius := Finset.single_le_sum hS hd
lemma noncoreCost_nonneg {d : MarkedDisk} (hd : 0≤d.radius) : 0≤d.noncoreCost := by
  unfold noncoreCost
  split <;> positivity
lemma noncore_radius_le_sum {S : Finset MarkedDisk} (hS : ∀d∈S,0≤d.radius)
    {d : MarkedDisk} (hd : d∈S) (hc : d.core=false) : d.radius≤∑e∈S,e.noncoreCost := by
  have hh := Finset.single_le_sum (fun e he => noncoreCost_nonneg (hS e he)) hd
  simpa [noncoreCost,hc] using hh
lemma sphere_avoids_holes {S : Finset MarkedDisk}
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    {d : MarkedDisk} (hd : d∈S) {z : ℂ} (hz : z∈Metric.sphere d.center d.radius) : z∉diskHoles S := by
  rintro hh
  obtain ⟨e,he,hze⟩ := mem_diskHoles.mp hh
  by_cases hde : d=e
  · subst e
    have hh' : dist z d.center<d.radius := hze
    have hz' : dist z d.center=d.radius := hz
    linarith
  · exact Set.disjoint_left.mp (hdis hd he hde) (Metric.sphere_subset_closedBall hz)
      (Metric.ball_subset_closedBall hze)
lemma closedBall_near_core {L : Set ℂ} {d : MarkedDisk} (hd : d.Valid L) (hc : d.core=true) :
    ∃x∈L,d.closedBall⊆Metric.ball x (2*d.radius) := by
  obtain ⟨x,hx,hxd⟩ := hd.2 hc
  refine ⟨x,hx,fun z hz => ?_⟩
  have hx' : dist d.center x<d.radius := by simpa only [ball,Metric.mem_ball,dist_comm] using hxd
  exact lt_of_le_of_lt (dist_triangle z d.center x) (by dsimp [closedBall] at hz; change dist z d.center≤d.radius at hz; linarith)
lemma sphere_norm_bound {d : MarkedDisk} {R : ℝ}
    (hmeet : (d.closedBall∩Metric.closedBall (0:ℂ) R).Nonempty) {z : ℂ}
    (hz : z∈Metric.sphere d.center d.radius) : dist z 0≤2*d.radius+R := by
  obtain ⟨a,ha,haR⟩ := hmeet
  have hza : dist z a≤2*d.radius := calc
    dist z a≤dist z d.center+dist d.center a := dist_triangle _ _ _
    _ ≤ 2*d.radius := by
      have hh : dist z d.center=d.radius := hz
      have ha' : dist d.center a≤d.radius := by simpa only [closedBall,Metric.mem_closedBall,dist_comm] using ha
      linarith
  exact (dist_triangle z a 0).trans (by change dist a 0≤R at haR; linarith)
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
def initialDisks (L C : Finset ℂ) (δ u : ℝ) : Finset MarkedDisk :=
  L.image (fun x => ⟨x,δ,true⟩) ∪ C.image (fun x => ⟨x,u,false⟩)
lemma mem_initialDisks {L C : Finset ℂ} {δ u : ℝ} {d : MarkedDisk} :
    d∈initialDisks L C δ u ↔ (∃x∈L,d=⟨x,δ,true⟩) ∨ (∃x∈C,d=⟨x,u,false⟩) := by
  simp [initialDisks,eq_comm]
lemma initialDisks_valid (L C : Finset ℂ) {δ u : ℝ} (hδ : 0<δ) (hu : 0<u) :
    ∀d∈initialDisks L C δ u,d.Valid (L : Set ℂ) := by
  intro d hd
  rcases mem_initialDisks.mp hd with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
  · exact ⟨hδ,fun _ => ⟨x,hx,Metric.mem_ball_self hδ⟩⟩
  · exact ⟨hu,by simp⟩
lemma initialDisks_sum (L C : Finset ℂ) (δ u : ℝ) :
    (∑d∈initialDisks L C δ u,d.radius)=(L.card:ℝ)*δ+(C.card:ℝ)*u ∧
    (∑d∈initialDisks L C δ u,d.noncoreCost)=(C.card:ℝ)*u := by
  have hd : Disjoint (L.image (fun x => (⟨x,δ,true⟩ : MarkedDisk)))
      (C.image (fun x => (⟨x,u,false⟩ : MarkedDisk))) := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    obtain ⟨x,hx,hxd⟩ := Finset.mem_image.mp hd
    obtain ⟨y,hy,hyd⟩ := Finset.mem_image.mp he
    have hh := congrArg MarkedDisk.core (hxd.trans hyd.symm)
    exact Bool.noConfusion hh
  have hi (r : ℝ) (b : Bool) : Function.Injective (fun x : ℂ => (⟨x,r,b⟩ : MarkedDisk)) := by
    intro x y h; exact congrArg MarkedDisk.center h
  simp only [initialDisks,Finset.sum_union hd]
  rw [Finset.sum_image (fun x _ y _ h => hi δ true h),Finset.sum_image (fun x _ y _ h => hi u false h),
      Finset.sum_image (fun x _ y _ h => hi δ true h),Finset.sum_image (fun x _ y _ h => hi u false h)]
  simp [noncoreCost]
lemma initial_core_cover (L C : Finset ℂ) (δ u : ℝ) {x z : ℂ} (hx : x∈L)
    (hz : z∈Metric.ball x δ) : z∈coreHoles (initialDisks L C δ u) := by
  exact mem_coreHoles.mpr ⟨⟨x,δ,true⟩,mem_initialDisks.mpr (Or.inl ⟨x,hx,rfl⟩),rfl,hz⟩
lemma initial_marked_cover (L C : Finset ℂ) (δ u : ℝ) {x z : ℂ} (hx : x∈C)
    (hz : z∈Metric.ball x u) : z∈diskHoles (initialDisks L C δ u) := by
  exact mem_diskHoles.mpr ⟨⟨x,u,false⟩,mem_initialDisks.mpr (Or.inr ⟨x,hx,rfl⟩),hz⟩
lemma holes_subset_of_cover {S T : Finset MarkedDisk}
    (hcov : ∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) :
    diskHoles S⊆diskHoles T ∧ coreHoles S⊆coreHoles T := by
  constructor
  · intro z hz
    obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
    obtain ⟨e,he,hde,_⟩ := hcov d hd
    exact mem_diskHoles.mpr ⟨e,he,hde hzd⟩
  · intro z hz
    obtain ⟨d,hd,hcd,hzd⟩ := mem_coreHoles.mp hz
    obtain ⟨e,he,hde,hc⟩ := hcov d hd
    exact mem_coreHoles.mpr ⟨e,he,hc hcd,hde hzd⟩
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
open MarkedDisk
/-- Actual small-hole maps on a fixed disk, with arbitrarily small total radii.
The core witnesses lie in the finite actual cyclic core; all other holes have been
filled by genuine tree extensions. -/
theorem small_hole_map {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (L : Finset ℂ)
    (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) (ht' : t<1/2) :
    ∃e>0,∀ε,0<ε → ε<e → ∃S : Finset MarkedDisk,
      (∀d∈S,d.Valid (L : Set ℂ)) ∧
      (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∑d∈S,d.radius)<t ∧
      ∃g : C(↥(Metric.closedBall (0:ℂ) 7 \ coreHoles S),GraphSpace (⊤ : SimpleGraph (Fin 5))),
        ∀z : ↥(Metric.closedBall (0:ℂ) 7 \ coreHoles S),z.val∉diskHoles S →
          (g z).val=thresholdMap c ε α z.val := by
  let δ : ℝ := t/(4*((L.card:ℝ)+1))
  have hδ : 0<δ := div_pos ht (by positivity)
  have hδeq : δ*(4*((L.card:ℝ)+1))=t := div_mul_cancel₀ _ (by positivity)
  have hδbudget : (L.card:ℝ)*δ<t/4 := by nlinarith
  let M := Metric.closedBall (0:ℂ) 8 \ ⋃x∈L,Metric.ball x δ
  have hM : IsCompact M := (isCompact_closedBall (0:ℂ) 8).diff
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball)
  have hf : ∀x∈M,(transitionGraph c x).IsAcyclic := by
    intro x hx
    by_contra hn
    exact hx.2 (mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hL x hx.1 hn,Metric.mem_ball_self hδ⟩⟩)
  obtain ⟨l,hl,hcharts⟩ := compact_forest_charts hc hα hα' M hM hf
  let κ := min (t/4) (l/6)
  have hκ : 0<κ := lt_min (by positivity) (by positivity)
  have hκt : κ≤t/4 := min_le_left _ _
  have hκl : κ≤l/6 := min_le_right _ _
  obtain ⟨e,he,hC⟩ := hcharts κ hκ
  refine ⟨e,he,fun ε hε hεe => ?_⟩
  obtain ⟨C,hCr,hCv⟩ := hC ε hε hεe
  let u := α*ε/4
  have hu : 0<u := by dsimp [u]; positivity
  obtain ⟨S,hS,hdis,hcov,hsum,hcost⟩ := MarkedDisk.separate
    (initialDisks L C δ u) (initialDisks_valid L C hδ hu) hκ
  have htot : (∑d∈S,d.radius)<t := by
    rw [(initialDisks_sum L C δ u).1] at hsum
    change (C.card:ℝ)*u<κ at hCr
    linarith
  have hnrad : ∀d∈S,d.core=false → 2*d.radius<l := by
    rw [(initialDisks_sum L C δ u).2] at hcost
    intro d hd hdf
    have hd' := noncore_radius_le_sum (fun a ha => (hS a ha).1.le) hd hdf
    change (C.card:ℝ)*u<κ at hCr
    linarith
  have hcover := holes_subset_of_cover hcov
  have hMof (z : ℂ) (hz : z∈Metric.closedBall (0:ℂ) 8) (hzS : z∉diskHoles S) : z∈M := by
    refine ⟨hz,?_⟩
    intro hh
    obtain ⟨x,hx⟩ := mem_iUnion.mp hh
    obtain ⟨hxL,hzx⟩ := mem_iUnion.mp hx
    exact hzS (hcover.1 (mem_diskHoles.mpr ⟨⟨x,δ,true⟩,
      mem_initialDisks.mpr (Or.inl ⟨x,hxL,rfl⟩),hzx⟩))
  have hmarked (z : ℂ) (hz : z∉diskHoles S) : z∉⋃x∈C,Metric.ball x u := by
    intro hh
    obtain ⟨x,hx⟩ := mem_iUnion.mp hh
    obtain ⟨hxC,hzx⟩ := mem_iUnion.mp hx
    exact hz (hcover.1 (initial_marked_cover L C δ u hxC hzx))
  let f : C(ℂ,Fin 5 → ℝ) := ⟨thresholdMap c ε α,continuous_thresholdMap hc hε hα'⟩
  have hg : ∀z∈Metric.closedBall (0:ℂ) 7,z∉diskHoles S →
      f z∈graphRealization (⊤ : SimpleGraph (Fin 5)) := by
    intro z hz hzS
    have hzM := hMof z (Metric.closedBall_subset_closedBall (by norm_num) hz) hzS
    obtain ⟨G,hG,hq⟩ := hCv z hzM
    exact graphRealization_mono le_top (hq z (Metric.mem_ball_self hl) (hmarked z hzS))
  have hb : ∀d∈S,d.core=false → (d.closedBall∩Metric.closedBall (0:ℂ) 7).Nonempty →
      ∃G : SimpleGraph (Fin 5),G.IsAcyclic ∧ ∀z∈Metric.sphere d.center d.radius,
        f z∈graphRealization G := by
    intro d hd hdf hmeet
    have hr := (hS d hd).1
    have hsph (z : ℂ) (hz : z∈Metric.sphere d.center d.radius) : z∈Metric.closedBall (0:ℂ) 8 := by
      have hzr := sphere_norm_bound hmeet hz
      have hd' := radius_le_sum (fun a ha => (hS a ha).1.le) hd
      change dist z 0≤8
      linarith
    obtain ⟨a,ha⟩ := (NormedSpace.sphere_nonempty (x:=d.center)).mpr hr.le
    have haM := hMof a (hsph a ha) (sphere_avoids_holes hdis hd ha)
    obtain ⟨G,hG,hq⟩ := hCv a haM
    refine ⟨G,hG,fun z hz => hq z ?_ (hmarked z (sphere_avoids_holes hdis hd hz))⟩
    have hza : dist z a≤2*d.radius := calc
      dist z a≤dist z d.center+dist d.center a := dist_triangle _ _ _
      _ = 2*d.radius := by
        have hz' : dist z d.center=d.radius := hz
        have ha' : dist d.center a=d.radius := by simpa only [Metric.mem_sphere,dist_comm] using ha
        rw [hz',ha']; ring
    exact hza.trans_lt (hnrad d hd hdf)
  obtain ⟨g,hg'⟩ := fill_noncore_disks (Metric.closedBall (0:ℂ) 7) S
    (fun d hd => (hS d hd).1) hdis f hg hb
  exact ⟨S,hS,hdis,htot,g,hg'⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical ENNReal
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Exception annuli for exact unit distances from the small closed disks. -/
def diskAnnulus (d : MarkedDisk) : Set ℂ :=
  Metric.closedBall d.center (1+d.radius) \ Metric.ball d.center (1-d.radius)
def holeAnnuli (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,diskAnnulus d
lemma diskAnnulus_measurable (d : MarkedDisk) : MeasurableSet (diskAnnulus d) :=
  Metric.isClosed_closedBall.measurableSet.diff Metric.isOpen_ball.measurableSet
lemma unit_from_disk_mem_annulus {d : MarkedDisk} {z q : ℂ}
    (hq : q∈d.closedBall) (hzq : dist z q=1) : z∈diskAnnulus d := by
  have hq' : dist q d.center≤d.radius := hq
  constructor
  · change dist z d.center≤1+d.radius
    exact (dist_triangle z q d.center).trans (by linarith)
  · change ¬ dist z d.center<1-d.radius
    have hh := dist_triangle z d.center q
    rw [dist_comm d.center q,hzq] at hh
    linarith
lemma volume_diskAnnulus {d : MarkedDisk} (h0 : 0≤d.radius) (h1 : d.radius≤1) :
    volume (diskAnnulus d)=ENNReal.ofReal (4*Real.pi*d.radius) := by
  have hsub : Metric.ball d.center (1-d.radius)⊆Metric.closedBall d.center (1+d.radius) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hvol (r : ℝ) (hr : 0≤r) : ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)=ENNReal.ofReal (r^2*Real.pi) := by
    rw [ENNReal.ofReal_mul (sq_nonneg r),ENNReal.ofReal_pow hr]
    congr 1
    rw [←NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  rw [diskAnnulus,measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet (by finiteness),
    Complex.volume_closedBall,Complex.volume_ball,hvol _ (by linarith),hvol _ (by linarith),
    ←ENNReal.ofReal_sub _ (by positivity : 0≤(1-d.radius)^2*Real.pi)]
  congr 1
  ring

lemma volume_holeAnnuli_le {S : Finset MarkedDisk}
    (hS : ∀d∈S,0≤d.radius ∧ d.radius≤1) :
    volume (holeAnnuli S)≤ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by
  calc
    volume (holeAnnuli S)≤∑d∈S,volume (diskAnnulus d) := measure_biUnion_finset_le S _
    _ = ∑d∈S,ENNReal.ofReal (4*Real.pi*d.radius) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact volume_diskAnnulus (hS d hd).1 (hS d hd).2
    _ = ENNReal.ofReal (∑d∈S,4*Real.pi*d.radius) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun d hd => mul_nonneg (by positivity) (hS d hd).1)]
    _ = ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by rw [Finset.mul_sum]
lemma unit_from_hole_mem_annuli {S : Finset MarkedDisk} {z q : ℂ}
    (hq : q∈diskHoles S) (hzq : dist z q=1) : z∈holeAnnuli S := by
  obtain ⟨d,hd,hqd⟩ := mem_diskHoles.mp hq
  exact mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hd,unit_from_disk_mem_annulus (Metric.ball_subset_closedBall hqd) hzq⟩⟩
lemma holeAnnuli_tendsto_zero (S : ℕ → Finset MarkedDisk)
    (hS : ∀n d,d∈S n → 0≤d.radius)
    (hlim : Tendsto (fun n => ∑d∈S n,d.radius) atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (S n))) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop,(∑d∈S n,d.radius)≤1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have hbound : ∀ᶠ n in atTop,volume (holeAnnuli (S n))≤ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius)) := by
    filter_upwards [hsmall] with n hn
    apply volume_holeAnnuli_le
    exact fun d hd => ⟨hS n d hd,(MarkedDisk.radius_le_sum (hS n) hd).trans hn⟩
  have ht : Tendsto (fun n => ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.const_mul (4*Real.pi))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro a ha
  filter_upwards [hbound,ENNReal.tendsto_nhds_zero.mp ht a ha] with n hn hn'
  exact hn.trans hn'
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
/-- Data actually constructed by the small-hole lemma. -/
structure HoleApprox (c : ℂ → Fin 5) (α : ℝ) (L : Finset ℂ) (t : ℝ) where
  ε : ℝ
  ε_pos : 0<ε
  ε_lt : ε<t
  disks : Finset MarkedDisk
  valid : ∀d∈disks,d.Valid (L : Set ℂ)
  disjoint : (disks : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
  sum_lt : (∑d∈disks,d.radius)<t
  map : C(↥(Metric.closedBall (0:ℂ) 7 \ coreHoles disks),GraphSpace (⊤ : SimpleGraph (Fin 5)))
  agrees : ∀z : ↥(Metric.closedBall (0:ℂ) 7 \ coreHoles disks),z.val∉diskHoles disks →
    (map z).val=thresholdMap c ε α z.val
lemma holeApprox_exists {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (L : Finset ℂ)
    (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) (ht' : t<1/2) : Nonempty (HoleApprox c α L t) := by
  obtain ⟨e,he,h⟩ := small_hole_map hc hα hα' L hL ht ht'
  let ε := min (e/2) (t/2)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  have hεe : ε<e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεt : ε<t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨S,hS,hdis,hsum,g,hg⟩ := h ε hε hεe
  exact ⟨⟨ε,hε,hεt,S,hS,hdis,hsum,g,hg⟩⟩
namespace HoleApprox
lemma cores_near {c : ℂ → Fin 5} {α t : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) : coreHoles a.disks⊆⋃x∈L,Metric.ball x (2*t) := by
  intro z hz
  obtain ⟨d,hd,hcd,hzd⟩ := mem_coreHoles.mp hz
  obtain ⟨x,hx,hsub⟩ := MarkedDisk.closedBall_near_core (a.valid d hd) hcd
  have hrad := MarkedDisk.radius_le_sum (fun e he => (a.valid e he).1.le) hd
  exact mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,
    Metric.ball_subset_ball (by linarith [a.sum_lt]) (hsub (Metric.ball_subset_closedBall hzd))⟩⟩
lemma ε_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (a n).ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => (a n).ε_pos.le) (fun n => (a n).ε_lt.le) ht
lemma sum_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∑d∈(a n).disks,d.radius) atTop (𝓝 0) :=
  squeeze_zero (fun n => Finset.sum_nonneg fun d hd => ((a n).valid d hd).1.le)
    (fun n => (a n).sum_lt.le) ht
lemma annuli_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (a n).disks)) atTop (𝓝 0) :=
  holeAnnuli_tendsto_zero _ (fun n d hd => ((a n).valid d hd).1.le) (sum_tendsto a ht)
end HoleApprox
end EuclideanFiveColor
end

end OAI
