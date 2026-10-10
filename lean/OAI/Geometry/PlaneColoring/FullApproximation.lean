import OAI.Geometry.PlaneColoring.ContinuumLimits
import OAI.Geometry.PlaneColoring.GraphPatches

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology TopologicalSpace MeasureTheory
namespace EuclideanFiveColor
/-- Compactness and the angular theorems force all sufficiently fine crossing graphs
to be forests. This is about actual compact bridges, not assumed interface data. -/
theorem eventually_forest_of_bridges {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} {ρ : ℝ} (hρ : 0<ρ)
    (D : ℕ → SimpleGraph (Fin 5)) {r ε : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀n,0<ε n)
    {H E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hnear : ∀n z q,q∈H n → dist z q=1 → z∈E n)
    {α : ℝ} (hα : 0<α)
    (hbridge : ∀n i j,(D n).Adj i j → ∃K : NonemptyCompacts ℂ,
      (K : Set ℂ)⊆Metric.closedBall x ρ ∧ IsPreconnected (K : Set ℂ) ∧
      (∃a∈K,dist a x≤r n) ∧ ((K : Set ℂ)∩Metric.sphere x ρ).Nonempty ∧
      (∀q∈K,q∉H n → α<diskAverage c (ε n) i q) ∧
      (∀q∈K,q∉H n → α<diskAverage c (ε n) j q)) :
    ∀ᶠ n in atTop,(D n).IsAcyclic := by
  have he : ∀i j : Fin 5,∀ᶠ n in atTop,(D n).Adj i j → CommonInterface c x i j := by
    intro i j
    by_cases hcommon : CommonInterface c x i j
    · exact Eventually.of_forall fun _ _ => hcommon
    · have hn : ∀ᶠ n in atTop,¬(D n).Adj i j := by
        by_contra hnot
        have hfreq : ∃ᶠ n in atTop,(D n).Adj i j := hnot
        obtain ⟨φ,hφ,hφD⟩ := subseq_forall_of_frequently (x:=fun n : ℕ => n) (p:=fun n => (D n).Adj i j) tendsto_id hfreq
        choose K hK hconn ha hout hi hj using fun n => hbridge (φ n) i j (hφD n)
        choose a haK har using ha
        have halim : Tendsto a atTop (𝓝 x) := by
          rw [tendsto_iff_dist_tendsto_zero]
          exact squeeze_zero (fun _ => dist_nonneg) har (hr.comp hφ)
        exact hcommon (commonInterface_of_compact_sequence hc hw hρ K hK hconn a haK halim hout
          (hε.comp hφ) (fun n => hpos (φ n)) (hE.comp hφ) (fun n => hnear (φ n)) hα i j hi hj)
      exact hn.mono fun _ hn hd => False.elim (hn hd)
  have hall : ∀ᶠ n in atTop,∀i j : Fin 5,(D n).Adj i j → CommonInterface c x i j :=
    eventually_all.mpr fun i => eventually_all.mpr (he i)
  filter_upwards [hall] with n hn
  exact commonInterface_graph_acyclic hc hw x (D n) hn
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology TopologicalSpace MeasureTheory ContinuousMap
namespace EuclideanFiveColor
lemma midpoint_threshold_labels {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) {q : ℂ} {i j : Fin 5} (hij : i≠j)
    (he : thresholdMap c ε α q=graphEdgePoint i j (1/2)) :
    α<diskAverage c ε i q ∧ α<diskAverage c ε j q := by
  constructor
  · apply (thresholdMap_pos hc hε hα q i).mp
    rw [he]
    norm_num [graphEdgePoint,graphVertex,hij,hij.symm]
  · apply (thresholdMap_pos hc hε hα q j).mp
    rw [he]
    norm_num [graphEdgePoint,graphVertex,hij,hij.symm]
/-- The actual continuous annulus maps eventually permit disk extensions. -/
theorem annulus_maps_eventually_forest {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} {R : ℝ} (hR : 0<R) {r ε : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀n,0<ε n)
    {H E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hnear : ∀n z q,q∈H n → dist z q=1 → z∈E n)
    {α : ℝ} (hα : 0<α) (hα' : α<1/5)
    (f : ∀n,C(planeAnnulus x (r n) R,GraphSpace (⊤ : SimpleGraph (Fin 5))))
    (hf : ∀n z,z.val∉H n → (f n z).val=thresholdMap c (ε n) α z.val) :
    ∀ᶠ n in atTop,(crossingGraph (fun z => (f n z).val)
      (annulusInner x (r n) R) (annulusOuter x (r n) R)).IsAcyclic := by
  apply eventually_forest_of_bridges hc hw hR _ hr hε hpos hE hnear hα
  intro n i j hij
  obtain ⟨K,hK,hconn,hval,hin,hout⟩ := hij.2
  let L : NonemptyCompacts ℂ := ⟨⟨Subtype.val '' K,hK.image continuous_subtype_val⟩,
    hconn.nonempty.image _⟩
  have hsub : (L : Set ℂ)⊆Metric.closedBall x R := by
    rintro q ⟨z,hz,rfl⟩
    exact z.property.1
  have hpre : IsPreconnected (L : Set ℂ) :=
    hconn.isPreconnected.image _ continuous_subtype_val.continuousOn
  have hanc : ∃a∈L,dist a x≤r n := by
    obtain ⟨a,ha,har⟩ := hin
    exact ⟨a.val,⟨a,ha,rfl⟩,har.le⟩
  have hout' : ((L : Set ℂ)∩Metric.sphere x R).Nonempty := by
    obtain ⟨a,ha,haR⟩ := hout
    exact ⟨a.val,⟨a,ha,rfl⟩,haR⟩
  refine ⟨L,hsub,hpre,hanc,hout',?_,?_⟩
  · rintro q ⟨z,hz,rfl⟩ hzH
    have he : thresholdMap c (ε n) α z.val=graphEdgePoint i j (1/2) := (hf n z hzH).symm.trans (hval hz)
    exact (midpoint_threshold_labels hc (hpos n) hα' hij.1 he).1
  · rintro q ⟨z,hz,rfl⟩ hzH
    have he : thresholdMap c (ε n) α z.val=graphEdgePoint i j (1/2) := (hf n z hzH).symm.trans (hval hz)
    exact (midpoint_threshold_labels hc (hpos n) hα' hij.1 he).2
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
/-- Actual finite disk pasting from a closed outside domain. Disks may cross the
boundary of the ambient compact region. -/
theorem finite_disk_paste {Y : Type u} [TopologicalSpace Y] (Q : Set ℂ)
    (S : Finset MarkedDisk)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (f : C(↥(Q \ diskHoles S),Y))
    (g : ∀d : S,C(d.val.closedBall,Y))
    (hb : ∀d : S,∀z : Metric.sphere d.val.center d.val.radius,∀hzQ : z.val∈Q,
      ∀hzS : z.val∉diskHoles S,
      g d ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f ⟨z.val,hzQ,hzS⟩) :
    ∃F : C(Q,Y),∀z : Q,∀hz : z.val∉diskHoles S,F z=f ⟨z.val,z.property,hz⟩ := by
  let Z : Option S → Set Q := fun i => match i with
    | none => {z | z.val∉diskHoles S}
    | some d => {z | z.val∈d.val.closedBall}
  have hZ : ∀i,IsClosed (Z i) := by
    intro i
    cases i with
    | none => exact (diskHoles_open S).isClosed_compl.preimage continuous_subtype_val
    | some d => exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hcov : ⋃i,Z i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : z.val∈diskHoles S
    · obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
      exact ⟨some ⟨d,hd⟩,Metric.ball_subset_closedBall hzd⟩
    · exact ⟨none,hz⟩
  let φ₀ : C(Z none,Y) := ⟨fun z => f ⟨z.val.val,z.val.property,z.property⟩,
    f.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ₁ (d : S) : C(Z (some d),Y) := ⟨fun z => g d ⟨z.val.val,z.property⟩,
    (g d).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀i,C(Z i,Y) := fun i => match i with | none => φ₀ | some d => φ₁ d
  have hbd (d : S) (z : Q) (h0 : z∈Z none) (h1 : z∈Z (some d)) :
      φ none ⟨z,h0⟩=φ (some d) ⟨z,h1⟩ := by
    have hn : z.val∉d.val.ball := fun hz => h0 (mem_diskHoles.mpr ⟨d.val,d.property,hz⟩)
    have hs : z.val∈Metric.sphere d.val.center d.val.radius :=
      le_antisymm h1 (le_of_not_gt hn)
    exact (hb d ⟨z.val,hs⟩ z.property h0).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some d => exact hbd d z hi hj
    | some d =>
      cases j with
      | none => exact (hbd d z hj hi).symm
      | some e =>
        by_cases hde : d=e
        · subst e; rfl
        · exact False.elim (Set.disjoint_left.mp (hdis d.property e.property
            (fun he => hde (Subtype.ext he))) hi hj)
  refine ⟨closedCoverMap Z hZ hcov φ hφ,fun z hz => ?_⟩
  exact closedCoverMap_apply Z hZ hcov φ hφ (i:=none) ⟨z,hz⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
namespace HoleApprox
def annulusMap {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) {x : ℂ} (hx : x∈activeCenters L) :
    C(planeAnnulus x (2*t) R,GraphSpace (⊤ : SimpleGraph (Fin 5))) :=
  ⟨fun z => a.map ⟨z.val,a.annulus_in_domain hR htR hsep hx z.property⟩,
    a.map.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
/-- Fill all the actual core holes simultaneously when their surrounding crossing
graphs are forests, retaining the threshold map outside the original and outer disks. -/
theorem fill_cores {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y)
    (hforest : ∀x (hx : x∈activeCenters L),
      (crossingGraph (fun z => (a.annulusMap hR htR hsep hx z).val)
        (annulusInner x (2*t) R) (annulusOuter x (2*t) R)).IsAcyclic) :
    ∃F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles a.disks →
        z.val∉diskHoles (centerDisks (activeCenters L) R) →
        (F z).val=thresholdMap c a.ε α z.val := by
  let D := centerDisks (activeCenters L) R
  have hdis : (D : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) :=
    centerDisks_disjoint fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  let f : C(↥(Metric.closedBall (0:ℂ) 5 \ diskHoles D),GraphSpace (⊤ : SimpleGraph (Fin 5))) :=
    ⟨fun z => a.map ⟨z.val,a.outside_centers_in_domain htR (htR.trans hR) z.property⟩,
      a.map.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hex (d : D) : ∃g : C(d.val.closedBall,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.sphere d.val.center d.val.radius,∀hzQ : z.val∈Metric.closedBall (0:ℂ) 5,
        ∀hzD : z.val∉diskHoles D,
        g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f ⟨z.val,hzQ,hzD⟩ := by
    obtain ⟨d,hd⟩ := d
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    obtain ⟨g,hg⟩ := annulus_forest_extension htR (a.annulusMap hR htR hsep hx) (hforest x hx)
    exact ⟨g,fun z _ _ => hg z⟩
  choose g hg using hex
  obtain ⟨F,hF⟩ := finite_disk_paste (Metric.closedBall (0:ℂ) 5) D hdis f g hg
  refine ⟨F,fun z hzS hzD => ?_⟩
  rw [hF z hzD]
  exact a.agrees _ hzS
/-- The common-exclusion limit contradiction applies to the constructed maps, so
all these actual core fillings exist eventually at any fixed separated outer scale. -/
theorem eventually_fill_cores {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {α R : ℝ} (hα : 0<α) (hα' : α<1/5) {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0))
    (hR0 : 0<R) (hR : R<1) (htR : ∀n,2*t n<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) :
    ∀ᶠ n in atTop,∃F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles (a n).disks →
        z.val∉diskHoles (centerDisks (activeCenters L) R) →
        (F z).val=thresholdMap c (a n).ε α z.val := by
  have hrad : Tendsto (fun n => 2*t n) atTop (𝓝 0) := by simpa using ht.const_mul 2
  have h (x : activeCenters L) : ∀ᶠ n in atTop,
      (crossingGraph (fun z => ((a n).annulusMap hR (htR n) hsep x.property z).val)
        (annulusInner x.val (2*t n) R) (annulusOuter x.val (2*t n) R)).IsAcyclic := by
    apply annulus_maps_eventually_forest hc hw hR0 hrad (ε_tendsto a ht)
      (fun n => (a n).ε_pos) (annuli_tendsto a ht)
      (fun _ _ _ => unit_from_hole_mem_annuli) hα hα'
      (fun n => (a n).annulusMap hR (htR n) hsep x.property)
    intro n z hz
    exact (a n).agrees _ hz
  have hall := eventually_all.mpr h
  filter_upwards [hall] with n hn
  exact (a n).fill_cores hR (htR n) hsep (fun x hx => hn ⟨x,hx⟩)
end HoleApprox
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
lemma diskHoles_union (S T : Finset MarkedDisk) : diskHoles (S∪T)=diskHoles S∪diskHoles T := by
  ext z
  simp only [mem_diskHoles,Finset.mem_union,mem_union]
  aesop
lemma disk_radius_sum_union_le (S T : Finset MarkedDisk) (h : ∀d∈S∪T,0≤d.radius) :
    (∑d∈S∪T,d.radius)≤(∑d∈S,d.radius)+(∑d∈T,d.radius) := by
  have hs : (∑d∈S∪T,d.radius)+(∑d∈S∩T,d.radius)=(∑d∈S,d.radius)+(∑d∈T,d.radius) := Finset.sum_union_inter
  have h0 : 0≤∑d∈S∩T,d.radius := Finset.sum_nonneg fun d hd =>
    h d (Finset.mem_union_left T (Finset.mem_inter.mp hd).1)
  linarith
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
/-- A global graph approximation, with actual small exceptional disks.
All fields will be constructed, not postulated as coloring hypotheses. -/
structure FullApprox (c : ℂ → Fin 5) (α t : ℝ) where
  ε : ℝ
  ε_pos : 0<ε
  ε_lt : ε<t
  disks : Finset MarkedDisk
  positive : ∀d∈disks,0<d.radius
  disjoint : (disks : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
  sum_lt : (∑d∈disks,d.radius)<t
  map : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5)))
  agrees : ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles disks →
    (map z).val=thresholdMap c ε α z.val
/-- The whole producer, using actual annular crossing fibers and all angular
contradictions: global graph approximants exist at arbitrarily small exception scales. -/
theorem fullApprox_exists_of_finite_core {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {α : ℝ} (hα : 0<α) (hα' : α<1/5)
    (L : Finset ℂ) (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) : Nonempty (FullApprox c α t) := by
  obtain ⟨s,hs,hsep⟩ := finite_centers_separation L
  let A := activeCenters L
  let R := min (s/4) (min (1/2) (t/(4*((A.card:ℝ)+1))))
  have hR0 : 0<R := lt_min (by positivity) (lt_min (by norm_num) (div_pos ht (by positivity)))
  have hRs : R ≤ s/4 := min_le_left _ _
  have hRhalf : R≤1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRt : R≤t/(4*((A.card:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R<1 := lt_of_le_of_lt hRhalf (by norm_num)
  have hRsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y := by
    intro x hx y hy hxy
    have hh := hsep x hx y hy hxy
    linarith
  have hRbudget : (A.card:ℝ)*R<t/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*((A.card:ℝ)+1))).mp hRt
    nlinarith
  let u : ℕ → ℝ := fun n => min (R/4) (min (t/4) (1/((n:ℝ)+1)))
  have hu : ∀n,0<u n := fun n => lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have huR : ∀n,2*u n<R := by
    intro n
    have hh : u n≤R/4 := min_le_left _ _
    linarith
  have hut : ∀n,u n<t := by
    intro n
    have hh : u n≤t/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hult : ∀n,u n<1/2 := by
    intro n
    have hh := huR n
    linarith
  have hulim : Tendsto u atTop (𝓝 0) :=
    squeeze_zero (fun n => (hu n).le) (fun n => (min_le_right _ _).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ∀n,HoleApprox c α L (u n) := fun n => Classical.choice (holeApprox_exists hc hα hα' L hL (hu n) (hult n))
  obtain ⟨n,F,hF⟩ := ((HoleApprox.eventually_fill_cores hc hw hα hα' a hulim hR0 hR1 huR hRsep).exists)
  let D := centerDisks A R
  have hD : ∀d∈D,d.Valid (L : Set ℂ) := by
    intro d hd
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    exact ⟨hR0,by simp⟩
  have hU : ∀d∈(a n).disks∪D,d.Valid (L : Set ℂ) := by
    intro d hd
    rcases Finset.mem_union.mp hd with hh|hh
    · exact (a n).valid d hh
    · exact hD d hh
  obtain ⟨S,hS,hdis,hcov,hsum,_⟩ := MarkedDisk.separate ((a n).disks∪D) hU (show 0<t/4 by positivity)
  have htS : (∑d∈S,d.radius)<t := by
    have hh := disk_radius_sum_union_le (a n).disks D (fun d hd => (hU d hd).1.le)
    have hDbudget : (∑d∈D,d.radius)<t/4 := by rw [centerDisks_sum]; exact hRbudget
    have hun : u n≤t/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [(a n).sum_lt]
  refine ⟨⟨(a n).ε,(a n).ε_pos,(a n).ε_lt.trans (hut n),S,
    fun d hd => (hS d hd).1,hdis,htS,F,?_⟩⟩
  intro z hz
  have hn : z.val∉diskHoles ((a n).disks∪D) := fun hh => hz ((MarkedDisk.holes_subset_of_cover hcov).1 hh)
  rw [diskHoles_union] at hn
  exact hF z (fun hh => hn (Or.inl hh)) (fun hh => hn (Or.inr hh))
/-- The finite core used above is obtained from the proved actual transition core
local-finiteness theorem; no regularity of the original coloring is added. -/
theorem fullApprox_exists {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {α : ℝ} (hα : 0<α) (hα' : α<1/5) {t : ℝ} (ht : 0<t) :
    Nonempty (FullApprox c α t) := by
  let hfin := cyclicCore_compact_finite c hc hw (isCompact_closedBall (0:ℂ) 8)
  exact fullApprox_exists_of_finite_core hc hw hα hα' hfin.toFinset
    (fun x hx hcyc => hfin.mem_toFinset.mpr ⟨hx,hcyc⟩) ht
end EuclideanFiveColor
end

end OAI
