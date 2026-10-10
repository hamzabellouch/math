import OAI.Combinatorics.HalvingLines.Continuity

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval

def Subwindows (K : Window) := {J : Window // carrier J ⊆ carrier K}
instance (K : Window) : Countable (Subwindows K) := by unfold Subwindows; infer_instance

lemma Converges.crossing_real_projection_disjoint {F : ℕ → Configuration} {L : Data}
    (h : Converges F L) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Disjoint (carrier A) (carrier B)) :
    (L.crossings A B : Measure Labels).map (fun z => ((z A : ℝ),(z B : ℝ))) ≪ volume := by
  rcases before_or_before hAB with hab | hba
  · exact h.crossing_real_projection hR hM hab
  · have hp : Measure.QuasiMeasurePreserving (fun z : Labels => ((z B : ℝ),(z A : ℝ)))
        (L.crossings B A : Measure Labels) volume :=
      ⟨by fun_prop,h.crossing_real_projection hR hM hba⟩
    have hswap : Measure.QuasiMeasurePreserving (Prod.swap : Point → Point) volume volume :=
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).quasiMeasurePreserving
    have hh := (hswap.comp hp).absolutelyContinuous
    simpa only [Function.comp_def, Prod.swap_prod_mk, ← h.crossings_comm A B] using hh

lemma Converges.rank_regular_ae {F : ℕ → Configuration} {L : Data} (_h : Converges F L)
    {K A B : Window} (ν : Measure Labels) (hp : ν ≪ (L.points : Measure Labels))
    (hproj : ν.map (pairCoordinates true A B) ≪ volume)
    (G : Subwindows K → Point → I)
    (hd : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (hid : ∀ i z, z ∈ (L.points : Measure Labels).support →
      ContinuousAt (G i) (pairCoordinates true A B z) →
      z i.val = G i (pairCoordinates true A B z)) :
    ∀ᵐ z ∂ν, ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z) ∧
      z i.val = G i (pairCoordinates true A B z) := by
  have hq : Measure.QuasiMeasurePreserving (pairCoordinates true A B) ν volume :=
    ⟨(continuous_pairCoordinates true A B).measurable,hproj⟩
  have hda := hq.ae ((ae_all_iff).mpr hd)
  have hs : ∀ᵐ z ∂ν, z ∈ (L.points : Measure Labels).support := hp.ae_le Measure.support_mem_ae
  filter_upwards [hda,hs] with z hz hzs i
  refine ⟨hz i,hid i z hzs ?_⟩
  exact ((hz i).continuousAt).codRestrict (fun x => (G i x).property)

lemma Converges.rank_independent_ae {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {K A B : Window} (G : Subwindows K → Point → I) :
    ∀ᵐ z ∂(L.edge : Measure Labels),
      (∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z) ∧
        z i.val = G i (pairCoordinates true A B z)) →
      ∀ J : Subwindows K, L.conditional z (carrier J.val) ≠ 0 →
        ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
          carrier j.val ⊆ carrier J.val ∧ Disjoint (carrier i.val) (carrier j.val) ∧
          Function.Injective (fun v : Point =>
            ((fderiv ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z)) v,
             (fderiv ℝ (fun x => (G j x : ℝ)) (pairCoordinates true A B z)) v)) := by
  let p := pairCoordinates true A B
  let S : Set Labels := {z | ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (p z) ∧
    z i.val = G i (p z)}
  have he : ∀ J : Subwindows K, ∀ᵐ z ∂(L.edge : Measure Labels), z ∈ S →
      L.conditional z (carrier J.val) ≠ 0 →
      ∃ q : CrossingPairs J.val,
        (fderiv ℝ (fun x => ((G ⟨q.val.1,q.property.1.trans J.property⟩ x : ℝ),
          (G ⟨q.val.2,q.property.2.1.trans J.property⟩ x : ℝ))) (p z)).det ≠ 0 := by
    intro J
    apply Transversality.independent_gradients_ae (L.edge : Measure Labels)
      (fun z => L.conditional z (carrier J.val)) (L.conditional.measurable_coe (measurable_carrier J.val))
      (fun q : CrossingPairs J.val => (L.crossings q.val.1 q.val.2 : Measure Labels))
      (by rw [← h.window_withDensity hR]; exact h.edge_crossing_ac E hR hC hcoeff herror hshort J.val)
      (fun q z => ((z q.val.1 : ℝ),(z q.val.2 : ℝ)))
      (fun _ => by fun_prop)
      (fun q => h.crossing_real_projection_disjoint hR hM q.property.2.2) p
      (fun q x => ((G ⟨q.val.1,q.property.1.trans J.property⟩ x : ℝ),
        (G ⟨q.val.2,q.property.2.1.trans J.property⟩ x : ℝ))) S
    · intro q z hz
      exact Prod.ext (congrArg Subtype.val (hz ⟨q.val.1,q.property.1.trans J.property⟩).2)
        (congrArg Subtype.val (hz ⟨q.val.2,q.property.2.1.trans J.property⟩).2)
    · intro q z hz
      exact ((hz _).1).prodMk ((hz _).1)
  filter_upwards [(ae_all_iff).mpr he] with z hz hreg J hJ
  obtain ⟨q,hq⟩ := hz J hreg hJ
  let i : Subwindows K := ⟨q.val.1,q.property.1.trans J.property⟩
  let j : Subwindows K := ⟨q.val.2,q.property.2.1.trans J.property⟩
  refine ⟨i,j,q.property.1,q.property.2.1,q.property.2.2,?_⟩
  have hder : fderiv ℝ (fun x => ((G i x : ℝ),(G j x : ℝ))) (p z) =
      (fderiv ℝ (fun x => (G i x : ℝ)) (p z)).prod (fderiv ℝ (fun x => (G j x : ℝ)) (p z)) :=
    ((hreg i).1.hasFDerivAt.prodMk (hreg j).1.hasFDerivAt).fderiv
  rw [hder] at hq
  let D := (fderiv ℝ (fun x => (G i x : ℝ)) (p z)).prod
    (fderiv ℝ (fun x => (G j x : ℝ)) (p z))
  change Function.Injective D
  apply (LinearMap.ker_eq_bot (f := D.toLinearMap)).mp
  by_contra hn
  exact hq (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

noncomputable def reflectSecond : Point ≃L[ℝ] Point :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

@[simp] lemma reflectSecond_apply (p : Point) : reflectSecond p = (p.1,-p.2) := rfl

lemma reflectSecond_signed (p : Point) : reflectSecond p = signedPair true p := rfl

noncomputable def Configuration.rankChart (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    OpenPartialHomeomorph Point Point :=
  let e := F.system.rankHomeomorph F.generic hAB hA hB
  let g : UnitOpen × UnitOpen → Point := Prod.map Subtype.val Subtype.val
  let hg : Topology.IsOpenEmbedding g :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal
  ((reflectSecond.toHomeomorph.isOpenEmbedding.comp hg).comp e.isOpenEmbedding).toOpenPartialHomeomorph _

lemma Configuration.rankChart_apply (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) (p : Point) :
    F.rankChart hAB hA hB p = pairCoordinates true A B (F.system.labels F.generic p) := by
  change reflectSecond (((F.system.rankHomeomorph F.generic hAB hA hB) p).1,
    ((F.system.rankHomeomorph F.generic hAB hA hB) p).2) = _
  obtain ⟨he1,he2⟩ := F.system.rankHomeomorph_coordinates F.generic hAB hA hB p
  rw [he1,he2]
  rfl

lemma Configuration.rankChart_source (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).source = univ := rfl

lemma Configuration.rankChart_target (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).target = Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  unfold Configuration.rankChart
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change Set.range (fun x : Point => reflectSecond
    (((F.system.rankHomeomorph F.generic hAB hA hB) x).1,
     ((F.system.rankHomeomorph F.generic hAB hA hB) x).2)) = _
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨((F.system.rankHomeomorph F.generic hAB hA hB) x).1.property,
      by dsimp; constructor <;> linarith [((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.1,
        ((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.2]⟩
  · intro hp
    let q : UnitOpen × UnitOpen := (⟨p.1,hp.1⟩,⟨-p.2,by constructor <;> linarith [hp.2.1,hp.2.2]⟩)
    refine ⟨(F.system.rankHomeomorph F.generic hAB hA hB).symm q,?_⟩
    dsimp only
    rw [Homeomorph.apply_symm_apply]
    simp [q]

noncomputable def Configuration.timeSlope (F : Configuration) (t : I) : ℝ :=
  F.system.slope ⟨cut (time F.R) t,Nat.lt_succ_of_le (cut_le _ _)⟩

lemma Configuration.timeSlope_before (F : Configuration) {J : Window} {t : I}
    (h : t ≤ lower J) : F.timeSlope t ≤ (F.system.timeWindow J).slope 0 := by
  apply F.system.increasing.monotone
  change cut (time F.R) t ≤ start F.R J+0
  simpa only [Nat.add_zero, start, TimeWindows.lower] using cut_mono (time F.R) h

lemma Configuration.timeSlope_after (F : Configuration) {J : Window} {t : I}
    (h : upper J ≤ t) : (F.system.timeWindow J).slope (Fin.last (length F.R J)) ≤ F.timeSlope t := by
  apply F.system.increasing.monotone
  change start F.R J+length F.R J ≤ cut (time F.R) t
  rw [start_add_length]
  exact cut_mono (time F.R) h

lemma coordinate_forward_before {l u s : ℝ} (C : Coordinate l u) (hs : s ≤ l)
    (x : Point) : Antitone (fun t : ℝ => C.value (x+t • (1,s))) := by
  intro a b hab
  have ht := C.translate_lower (x.1+a) (x.2+a*s) (b-a) (sub_nonneg.mpr hab)
  have hv := (C.strict_vertical (x.1+b)).monotone
    (show x.2+b*s ≤ x.2+a*s+l*(b-a) by nlinarith)
  have he : x.1+a+(b-a)=x.1+b := by ring
  rw [he] at ht
  change C.value (x.1+b*1,x.2+b*s) ≤ C.value (x.1+a*1,x.2+a*s)
  simpa only [mul_one] using hv.trans ht

lemma coordinate_forward_after {l u s : ℝ} (C : Coordinate l u) (hs : u ≤ s)
    (x : Point) : Monotone (fun t : ℝ => C.value (x+t • (1,s))) := by
  intro a b hab
  have ht := C.translate_upper (x.1+a) (x.2+a*s) (b-a) (sub_nonneg.mpr hab)
  have hv := (C.strict_vertical (x.1+b)).monotone
    (show x.2+a*s+u*(b-a) ≤ x.2+b*s by nlinarith)
  have he : x.1+a+(b-a)=x.1+b := by ring
  rw [he] at ht
  change C.value (x.1+a*1,x.2+a*s) ≤ C.value (x.1+b*1,x.2+b*s)
  simpa only [mul_one] using ht.trans hv

lemma Configuration.rank_forward_before (F : Configuration) {J : Window} (hJ : 0 < length F.R J)
    {t : I} (ht : t ≤ lower J) (x : Point) :
    Antitone (fun r : ℝ => (F.system.labels F.generic (x+r • (1,F.timeSlope t)) J : ℝ)) := by
  have hlt := (F.timeSlope_before ht).trans (F.system.rankGraphs F.generic J hJ).lower_lt.le
  have h := coordinate_forward_before (F.system.rankCoordinate F.generic J hJ) hlt x
  simpa only [F.system.rankCoordinate_value] using h

lemma Configuration.rank_forward_after (F : Configuration) {J : Window} (hJ : 0 < length F.R J)
    {t : I} (ht : upper J ≤ t) (x : Point) :
    Monotone (fun r : ℝ => (F.system.labels F.generic (x+r • (1,F.timeSlope t)) J : ℝ)) := by
  have hlt := (F.system.rankGraphs F.generic J hJ).upper_lt.le.trans (F.timeSlope_after ht)
  have h := coordinate_forward_after (F.system.rankCoordinate F.generic J hJ) hlt x
  simpa only [F.system.rankCoordinate_value] using h

end PlanarHalving.RankLimits
namespace PlanarHalving.Directions
open Set Filter Metric
open scoped Topology

lemma allowed_nonempty_of_approx {ι : Type*} (Q : Plane ≃L[ℝ] Plane)
    (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ) (t : ℝ)
    (happrox : ∀ S : Finset ι, ∀ ε : ℝ, 0 < ε → ∃ x ∈ Icc (0:ℝ) 1,
      ∀ i ∈ S, (hi i < t → -ε ≤ g i (Q (simplex x))) ∧
        (t < lo i → g i (Q (simplex x)) ≤ ε)) :
    (allowed Q g lo hi t).Nonempty := by
  classical
  let T (i : ι) : Set ℝ := {x | (hi i < t → 0 ≤ g i (Q (simplex x))) ∧
    (t < lo i → g i (Q (simplex x)) ≤ 0)}
  have hc (i : ι) : Continuous (fun x : ℝ => g i (Q (simplex x))) := by
    exact (g i).continuous.comp (Q.continuous.comp (continuous_id.prodMk (continuous_const.sub continuous_id)))
  have hcl (i : ι) : IsClosed (T i) := by
    change IsClosed ({x | hi i < t → 0 ≤ g i (Q (simplex x))} ∩
      {x | t < lo i → g i (Q (simplex x)) ≤ 0})
    apply IsClosed.inter
    · by_cases h : hi i < t
      · simpa only [h, true_implies] using isClosed_le continuous_const (hc i)
      · simpa only [h, false_implies, ofPred_true] using (isClosed_univ : IsClosed (univ : Set ℝ))
    · by_cases h : t < lo i
      · simpa only [h, true_implies] using isClosed_le (hc i) continuous_const
      · simpa only [h, false_implies, ofPred_true] using (isClosed_univ : IsClosed (univ : Set ℝ))
  have hfin (S : Finset ι) : ((Icc (0:ℝ) 1) ∩ ⋂ i ∈ S, T i).Nonempty := by
    have ha (n : ℕ) := happrox S ((n+1:ℝ)⁻¹) (by positivity)
    choose x hx hxi using ha
    obtain ⟨a,ha,φ,hφ,hxa⟩ := isCompact_Icc.tendsto_subseq hx
    refine ⟨a,ha,?_⟩
    simp only [mem_iInter]
    intro i hiS
    have he : Tendsto (fun n : ℕ => ((φ n+1:ℝ)⁻¹)) atTop (𝓝 0) :=
      by
        have he' : Tendsto (fun n : ℕ => 1 / (n+1:ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div, Function.comp_def] using he'.comp hφ.tendsto_atTop
    constructor
    · intro hit
      exact le_of_tendsto_of_tendsto (by simpa only [neg_zero] using he.neg) ((hc i).tendsto a |>.comp hxa)
        (Eventually.of_forall fun n => (hxi (φ n) i hiS).1 hit)
    · intro hti
      exact le_of_tendsto_of_tendsto ((hc i).tendsto a |>.comp hxa) he
        (Eventually.of_forall fun n => (hxi (φ n) i hiS).2 hti)
  obtain ⟨x,hx,hxt⟩ := isCompact_Icc.inter_iInter_nonempty T hcl hfin
  exact ⟨x,hx,fun i => mem_iInter.mp hxt i⟩

lemma ray_exit_at_radius (f : OpenPartialHomeomorph Plane Plane) (hs : f.source=univ)
    {p v : Plane} (hp : p ∈ f.target) (hv : v ≠ 0) {h : ℝ} (hh : 0 < h)
    (hball : closedBall p h ⊆ f.target) :
    ∃ r : ℝ, 0 ≤ r ∧ dist (f (f.symm p+r • v)) p = h := by
  have hfp := f.right_inv hp
  obtain ⟨T,hT,hfar⟩ := Zoom.ray_image_leaves_ball f hs (f.symm p) v hv h
    (by simpa only [hfp] using hball)
  rw [hfp] at hfar
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [← hs] using f.continuousOn)
  have hc : Continuous (fun r : ℝ => dist (f (f.symm p+r • v)) p) :=
    (hf.comp (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc hT hc.continuousOn
    (show h ∈ Icc (dist (f (f.symm p+0 • v)) p) (dist (f (f.symm p+T • v)) p) from
      ⟨by simpa [hfp] using hh.le,hfar.le⟩)
  exact ⟨r,hr.1,he⟩

lemma chord_firstOrder {f : Plane → ℝ} {D : Plane →L[ℝ] ℝ} {c ε h : ℝ}
    {p x y : Plane} (hx : dist (f x) (c+D (x-p)) < ε*h)
    (hy : dist (f y) (c+D (y-p)) < ε*h) :
    |(f y-f x)-D (y-x)| < 2*ε*h := by
  have he : D (y-x)=D (y-p)-D (x-p) := by rw [← map_sub]; congr 1; abel
  rw [he]
  rw [Real.dist_eq,abs_lt] at hx hy
  rw [abs_lt]
  constructor <;> linarith

end PlanarHalving.Directions
namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

noncomputable def reflectFirst : Point ≃L[ℝ] Point :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] lemma reflectFirst_apply (p : Point) : reflectFirst p = (-p.1,p.2) := rfl

lemma rank_firstOrder_filter (F : ℕ → Configuration) (A B C : Window) (G : Point → I)
    (hjoint : ∀ p, ContinuousAt G p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B C q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G p)))
    (hGaed : ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G x : ℝ)) p)
    {p : Point} (hd : DifferentiableAt ℝ (fun x => (G x : ℝ)) p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
      dist ((F n).extendedRank true A B C x : ℝ)
        ((G p : ℝ) + (fderiv ℝ (fun x => (G x : ℝ)) p) (x-p)) < ε*h := by
  obtain ⟨δ,hδ,hbound⟩ := RankLimit.firstOrder_of_joint
    (fun n => fun x y hxy => (F n).extendedRank_monotone true A B C hxy)
    (fun x hx => (continuous_subtype_val.tendsto _).comp
      (hjoint x (hx.codRestrict (fun x => (G x).property)))) hGaed hd.hasFDerivAt hR hε
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds hδ) : ∀ᶠ h in 𝓝[>] (0:ℝ), h < δ)] with h hh hhd
  exact hbound h hh hhd

theorem actual_allowed_nonempty {ι : Type*} (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {A B : Window} (hAB : Before A B) (C : ι → Window)
    (hC : ∀ i, Before (C i) A ∧ Before (C i) B)
    (G : ι → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B (C i) q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    {p : Point} (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) :
    (Directions.allowed reflectFirst (fun i => fderiv ℝ (fun x => (G i x : ℝ)) p)
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t).Nonempty := by
  classical
  apply Directions.allowed_nonempty_of_approx
  intro S ε hε
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)
  have hfirst : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ i ∈ S, ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p h, dist ((F n).extendedRank true A B (C i) x : ℝ)
        ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    apply (Filter.eventually_all_finset S).mpr
    intro i _
    simpa only [one_mul] using rank_firstOrder_filter F A B (C i) (G i)
      (hjoint i) (hGaed i) (hd i) (R:=1) (by norm_num) (half_pos hε)
  have hall : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < h ∧ h < r ∧
      ∀ i ∈ S, ∀ᶠ n in atTop, ∀ x ∈ closedBall p h,
        dist ((F n).extendedRank true A B (C i) x : ℝ)
          ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr), hfirst]
      with h hh hhr hhn
    exact ⟨hh,hhr,hhn⟩
  obtain ⟨h,hh,hhr,hhn⟩ := hall.exists
  have hn : ∀ᶠ n in atTop, 0 < length (F n).R A ∧ 0 < length (F n).R B ∧
      ∀ i ∈ S, 0 < length (F n).R (C i) ∧
        ∀ x ∈ closedBall p h, dist ((F n).extendedRank true A B (C i) x : ℝ)
          ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B,
      (Filter.eventually_all_finset S).mpr (fun i hi =>
        (eventually_length_pos _ hR (C i)).and (hhn i hi))] with n hA hB hS
    exact ⟨hA,hB,hS⟩
  obtain ⟨n,hA,hB,hS⟩ := hn.exists
  let f := (F n).rankChart hAB hA hB
  have htarget : f.target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := (F n).rankChart_target hAB hA hB
  have hp' : p ∈ f.target := by rwa [htarget]
  have hball : closedBall p h ⊆ f.target := by
    rw [htarget]
    exact fun x hx => hrsub ((Metric.mem_closedBall.mp hx).trans_lt hhr)
  have hv : (1,(F n).timeSlope t) ≠ (0:Point) := by intro he; have := congrArg Prod.fst he; norm_num at this
  obtain ⟨s,hs,hexit⟩ := Directions.ray_exit_at_radius f ((F n).rankChart_source hAB hA hB) hp' hv hh hball
  let x := f.symm p
  let y := x+s • (1,(F n).timeSlope t)
  let d := f y-p
  have hfx : f x=p := f.right_inv hp'
  have hd1 : d.1 ≤ 0 := by
    have hm := (F n).rank_forward_before hA htA x hs
    have he (q : Point) : (f q).1 = (F n).system.labels (F n).generic q A := by
      rw [(F n).rankChart_apply]; rfl
    change (f y).1-p.1 ≤ 0
    rw [← hfx,he,he]
    exact sub_nonpos.mpr (by simpa only [zero_smul,add_zero] using hm)
  have hd2 : 0 ≤ d.2 := by
    have hm := (F n).rank_forward_before hB htB x hs
    have he (q : Point) : (f q).2 = -(F n).system.labels (F n).generic q B := by
      rw [(F n).rankChart_apply]; rfl
    have hd' : d.2= -(F n).system.labels (F n).generic y B +
        (F n).system.labels (F n).generic x B := by
      change (f y).2-p.2=_
      rw [← hfx,he,he]
      ring
    rw [hd']
    simpa only [zero_smul,add_zero,zero_add, sub_eq_add_neg,add_comm,y] using sub_nonneg.mpr hm
  have hnorm : ‖d‖=h := by simpa only [d,y,x,dist_eq_norm] using hexit
  let a : ℝ := -d.1+d.2
  have hha : h ≤ a := by
    rw [← hnorm,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonpos hd1,abs_of_nonneg hd2]
    exact max_le (by dsimp [a]; linarith) (by dsimp [a]; linarith)
  have ha : 0 < a := hh.trans_le hha
  let z : ℝ := -d.1/a
  have hz0 : 0 ≤ z := div_nonneg (neg_nonneg.mpr hd1) ha.le
  have hz1 : z ≤ 1 := (div_le_one ha).mpr (by dsimp [a]; linarith)
  have hdz : d = a • reflectFirst (Directions.simplex z) := by
    ext <;> dsimp [reflectFirst,Directions.simplex,z]
    · field_simp [ha.ne'];
    · field_simp [ha.ne']; dsimp [a]; ring
  refine ⟨z,⟨hz0,hz1⟩,?_⟩
  intro i hi
  let D := fderiv ℝ (fun x => (G i x : ℝ)) p
  have hCi := (hS i hi).1
  have heq (q : Point) : (F n).extendedRank true A B (C i) (f q) =
      (F n).system.labels (F n).generic q (C i) := by
    rw [(F n).rankChart_apply]
    exact (F n).extendedRank_eq true hAB (hC i) hA hB hCi q
  have hchord := Directions.chord_firstOrder
    (f := fun q => ((F n).extendedRank true A B (C i) q : ℝ)) (D := D)
    (c := (G i p : ℝ)) (p := p) (ε := ε/2) (h := h) (x := f x) (y := f y)
    ((hS i hi).2 (f x) (by rw [hfx]; exact mem_closedBall_self hh.le))
    ((hS i hi).2 (f y) hexit.le)
  rw [heq x,heq y,hfx] at hchord
  change |((F n).system.labels (F n).generic y (C i) : ℝ)-
    ((F n).system.labels (F n).generic x (C i) : ℝ)-D d| < 2*(ε/2)*h at hchord
  have hchord' := abs_lt.mp hchord
  have hDd : D d=a*D (reflectFirst (Directions.simplex z)) := by rw [hdz,map_smul]; rfl
  constructor
  · intro hit
    have hm := (F n).rank_forward_after hCi (show upper (C i) ≤ t from hit.le) x hs
    simp only [zero_smul,add_zero] at hm
    have hb : -ε*h ≤ D d := by linarith
    rw [hDd] at hb
    change -ε ≤ D (reflectFirst (Directions.simplex z))
    by_contra hnz
    have hz' := lt_of_not_ge hnz
    have hm' := mul_lt_mul_of_pos_left hz' ha
    nlinarith [mul_le_mul_of_nonneg_left hha hε.le]
  · intro hti
    have hm := (F n).rank_forward_before hCi (show t ≤ lower (C i) from hti.le) x hs
    simp only [zero_smul,add_zero] at hm
    have hb : D d ≤ ε*h := by linarith
    rw [hDd] at hb
    change D (reflectFirst (Directions.simplex z)) ≤ ε
    by_contra hnz
    have hz' := lt_of_not_ge hnz
    have hm' := mul_lt_mul_of_pos_left hz' ha
    nlinarith [mul_le_mul_of_nonneg_left hha hε.le]

end PlanarHalving.RankLimits

end OAI
