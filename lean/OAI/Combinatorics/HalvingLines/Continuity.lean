import OAI.Combinatorics.HalvingLines.Derivatives

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped unitInterval Topology

noncomputable def lower (J : Window) : I := UniformPartition.boundary (2^J.1) J.2.castSucc
noncomputable def upper (J : Window) : I := UniformPartition.boundary (2^J.1) J.2.succ

lemma lower_lt_upper (J : Window) : lower J < upper J := by
  change (J.2 : ℝ)/(2^J.1 : ℕ) < ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)
  apply div_lt_div_of_pos_right _ (by positivity)
  simp

lemma upper_sub_lower (J : Window) : (upper J : ℝ) - (lower J : ℝ) = 1/(2:ℝ)^J.1 := by
  simp only [upper, lower, UniformPartition.boundary, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma Ioo_subset_carrier (J : Window) : Ioo (lower J) (upper J) ⊆ carrier J := by
  intro t ht
  unfold carrier UniformPartition.cell
  split_ifs
  · exact ⟨ht.1.le, ht.2.le⟩
  · exact ⟨ht.1.le, ht.2⟩

lemma carrier_subset_Icc (J : Window) : carrier J ⊆ Icc (lower J) (upper J) := by
  intro t ht
  unfold carrier UniformPartition.cell at ht
  split_ifs at ht
  · exact ht
  · exact ⟨ht.1, ht.2.le⟩

lemma closure_carrier (J : Window) : closure (carrier J) = Icc (lower J) (upper J) := by
  unfold carrier UniformPartition.cell
  split_ifs
  · exact isClosed_Icc.closure_eq
  · exact closure_Ico (lower_lt_upper J).ne

lemma endpoints_of_subset {J K : Window} (h : carrier J ⊆ carrier K) :
    lower K ≤ lower J ∧ upper J ≤ upper K := by
  have hh := closure_mono h
  rw [closure_carrier, closure_carrier] at hh
  exact ⟨(hh ⟨le_rfl,(lower_lt_upper J).le⟩).1,
    (hh ⟨(lower_lt_upper J).le,le_rfl⟩).2⟩

lemma before_or_before {A B : Window} (h : Disjoint (carrier A) (carrier B)) :
    Before A B ∨ Before B A := by
  by_contra hn
  have hn' : upper B > lower A ∧ upper A > lower B := by
    simpa only [Before, lower, upper, not_or, not_le, and_comm] using hn
  have hlt : max (lower A) (lower B) < min (upper A) (upper B) := by
    exact max_lt_iff.mpr ⟨lt_min (lower_lt_upper A) hn'.1,
      lt_min hn'.2 (lower_lt_upper B)⟩
  obtain ⟨t,ht1,ht2⟩ := exists_between hlt
  exact Set.disjoint_left.mp h (Ioo_subset_carrier A ⟨(le_max_left _ _).trans_lt ht1,
      ht2.trans_le (min_le_left _ _)⟩)
    (Ioo_subset_carrier B ⟨(le_max_right _ _).trans_lt ht1,ht2.trans_le (min_le_right _ _)⟩)

lemma before_of_separated {K H C A : Window} (hKH : upper K < lower H)
    (hC : carrier C ⊆ carrier K) (hA : carrier A ⊆ carrier H) : Before C A := by
  exact ((endpoints_of_subset hC).2.trans hKH.le).trans (endpoints_of_subset hA).1

lemma ae_avoid_boundaries (μ : Measure I) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ∀ m (i : Fin (2^m+1)), t ≠ UniformPartition.boundary (2^m) i := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro i
  exact μ.ae_ne _

lemma exists_separated_positive (μ : Measure I) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ K H : Window, (0 : ℝ) < lower K ∧ upper K < lower H ∧ (upper H : ℝ) < 1 ∧
      μ (carrier K) ≠ 0 ∧ μ (carrier H) ≠ 0 := by
  have he0 : ∀ᵐ t ∂μ, t ≠ (0 : I) := μ.ae_ne _
  have he1 : ∀ᵐ t ∂μ, t ≠ (1 : I) := μ.ae_ne _
  have hes : ∀ᵐ t ∂μ, t ∈ μ.support := μ.support_mem_ae
  obtain ⟨x,hxs,hxb,hx0,hx1⟩ :=
    (hes.and ((ae_avoid_boundaries μ).and (he0.and he1))).exists
  have hne : ∀ᵐ t ∂μ, t ≠ x := μ.ae_ne _
  obtain ⟨y,hys,hyb,hy0,hy1,hyx⟩ :=
    (hes.and ((ae_avoid_boundaries μ).and (he0.and (he1.and hne)))).exists
  have base (x y : I) (hxs : x ∈ μ.support) (hys : y ∈ μ.support)
      (hxb : ∀ m (i : Fin (2^m+1)), x ≠ UniformPartition.boundary (2^m) i)
      (hyb : ∀ m (i : Fin (2^m+1)), y ≠ UniformPartition.boundary (2^m) i)
      (hx0 : x ≠ 0) (hy1 : y ≠ 1) (hxy : x < y) :
      ∃ K H : Window, (0 : ℝ) < lower K ∧ upper K < lower H ∧ (upper H : ℝ) < 1 ∧
        μ (carrier K) ≠ 0 ∧ μ (carrier H) ≠ 0 := by
    have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (by
      intro hh; exact hx0 (Subtype.ext hh.symm))
    have hylt : (y : ℝ) < 1 := lt_of_le_of_ne y.property.2 (by
      intro hh; exact hy1 (Subtype.ext hh))
    have hxy' : (x : ℝ) < (y : ℝ) := hxy
    have hmesh : Tendsto (fun m : ℕ => 1/(2:ℝ)^m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have he := hmesh.eventually (gt_mem_nhds (show 0 < min (x : ℝ) (min (1-(y:ℝ)) (((y:ℝ)-x)/2)) by positivity))
    obtain ⟨m,hm⟩ := he.exists
    have hm1 := (lt_min_iff.mp hm).1
    have hm2 := (lt_min_iff.mp (lt_min_iff.mp hm).2).1
    have hm3 := (lt_min_iff.mp (lt_min_iff.mp hm).2).2
    obtain ⟨i,hi⟩ := UniformPartition.mem_some_cell (2^m) x
    obtain ⟨j,hj⟩ := UniformPartition.mem_some_cell (2^m) y
    let K : Window := ⟨m,i⟩
    let H : Window := ⟨m,j⟩
    have hk := carrier_subset_Icc K hi
    have hh := carrier_subset_Icc H hj
    have hki : x ∈ Ioo (lower K) (upper K) :=
      ⟨lt_of_le_of_ne hk.1 (Ne.symm (hxb m i.castSucc)), lt_of_le_of_ne hk.2 (hxb m i.succ)⟩
    have hhi : y ∈ Ioo (lower H) (upper H) :=
      ⟨lt_of_le_of_ne hh.1 (Ne.symm (hyb m j.castSucc)), lt_of_le_of_ne hh.2 (hyb m j.succ)⟩
    have kw := upper_sub_lower K
    have hw := upper_sub_lower H
    have hk1 : (lower K : ℝ) ≤ x := hk.1
    have hk2 : (x : ℝ) ≤ upper K := hk.2
    have hh1 : (lower H : ℝ) ≤ y := hh.1
    have hh2 : (y : ℝ) ≤ upper H := hh.2
    refine ⟨K,H,?_,?_,?_,?_,?_⟩
    · dsimp [K] at kw
      linarith
    · change (upper K : ℝ) < lower H
      dsimp [K] at kw
      dsimp [H] at hw
      linarith
    · dsimp [H] at hw
      linarith
    · exact ne_of_gt ((measure_mono (Ioo_subset_carrier K)).trans_lt' ((Measure.mem_support_iff_forall x).mp hxs _ (Ioo_mem_nhds hki.1 hki.2)))
    · exact ne_of_gt ((measure_mono (Ioo_subset_carrier H)).trans_lt' ((Measure.mem_support_iff_forall y).mp hys _ (Ioo_mem_nhds hhi.1 hhi.2)))
  rcases lt_or_gt_of_ne hyx with h | h
  · exact base y x hys hxs hyb hxb hy0 hx1 h
  · exact base x y hxs hys hxb hyb hx0 hy1 h

end PlanarHalving.TimeWindows
namespace PlanarHalving.Batches
open Set MeasureTheory TimeWindows Limits
variable {n R k a : ℕ} {P : Fin n → Point}
lemma System.windowCrossings_comm (S : @System n R k a P) [NeZero R] (A B : Window) :
    S.windowCrossings A B = S.windowCrossings B A := by
  classical
  unfold System.windowCrossings
  congr 1
  funext w
  apply propext
  tauto

lemma System.windowCrossMeasure_comm (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) : S.windowCrossMeasure A B z = S.windowCrossMeasure B A z := by
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro U hU
  apply NNReal.coe_injective
  rw [S.windowCrossMeasure_apply A B z hU,S.windowCrossMeasure_apply B A z hU]
  rw [System.crossingsIn,System.crossingsIn,S.windowCrossings_comm A B]
end PlanarHalving.Batches

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped unitInterval Topology

lemma Converges.crossings_comm {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (A B : Window) : L.crossings A B = L.crossings B A := by
  apply tendsto_nhds_unique (h.crossings A B)
  convert h.crossings B A using 1
  funext n
  exact (F n).system.windowCrossMeasure_comm A B _

lemma unitPair_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun p : I × I => ((p.1 : ℝ),(p.2 : ℝ))) volume volume := by
  have hi : Measure.QuasiMeasurePreserving ((↑) : I → ℝ) volume volume :=
    unitInterval.measurePreserving_coe.quasiMeasurePreserving.mono_right (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self))
  exact QuasiMeasurePreserving.prodMap hi hi

lemma signedPair_measurePreserving (b : Bool) : MeasurePreserving (signedPair b) volume volume := by
  cases b
  · exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  · exact (MeasurePreserving.id _).prod (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma Converges.crossing_real_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Before A B) :
    (L.crossings A B : Measure Labels).map (fun z => ((z A : ℝ),(z B : ℝ))) ≪ volume := by
  have hp : Measure.QuasiMeasurePreserving (fun z : Labels => (z A,z B))
      (L.crossings A B : Measure Labels) volume :=
    ⟨(continuous_apply A |>.prodMk (continuous_apply B)).measurable,
      Measure.absolutelyContinuous_of_le (h.crossing_projection hR hM hAB)⟩
  exact (unitPair_quasiMeasurePreserving.comp hp).absolutelyContinuous

lemma Converges.crossing_signed_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    (b : Bool) {A B : Window} (hAB : Before A B) :
    (L.crossings A B : Measure Labels).map (pairCoordinates b A B) ≪ volume := by
  have hp : Measure.QuasiMeasurePreserving (fun z : Labels => ((z A : ℝ),(z B : ℝ)))
      (L.crossings A B : Measure Labels) volume :=
    ⟨by fun_prop,h.crossing_real_projection hR hM hAB⟩
  exact ((signedPair_measurePreserving b).quasiMeasurePreserving.comp hp).absolutelyContinuous

lemma Converges.window_withDensity {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeWindow J : Measure Labels) = (L.edge : Measure Labels).withDensity
      (fun z => L.conditional z (carrier J)) := by
  ext U hU
  rw [withDensity_apply _ hU, Data.edge_toMeasure, Data.conditional,
    Measure.setLIntegral_condKernel_eq_measure_prod hU (measurable_carrier J)]
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

lemma Converges.edge_probability {F : ℕ → Configuration} {L : Data} (h : Converges F L) :
    IsProbabilityMeasure (L.edge : Measure Labels) := by
  constructor
  rw [Data.edge,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ,← FiniteMeasure.ennreal_mass,h.edgeTime_mass]
  rfl

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimit
open Filter Set Metric MeasureTheory
open scoped Topology

lemma dense_strict_brackets {S : Set Point} (hS : Dense S) {p : Point} {U : Set Point}
    (hU : U ∈ 𝓝 p) :
    (∃ l ∈ S ∩ U, l.1 < p.1 ∧ l.2 < p.2) ∧
    (∃ u ∈ S ∩ U, p.1 < u.1 ∧ p.2 < u.2) := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hb : ‖(r/2,r/2)‖ < r := by
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_of_pos (half_pos hr),max_self]
    linarith only [hr]
  constructor
  · obtain ⟨l,hlS,hl⟩ := hS.exists_mem_open
      ((isOpen_ball.inter (isOpen_lt continuous_fst continuous_const)).inter
        (isOpen_lt continuous_snd continuous_const))
      (show ((ball p r ∩ {x : Point | x.1 < p.1}) ∩ {x : Point | x.2 < p.2}).Nonempty from
        ⟨p-(r/2,r/2),⟨⟨by simpa [Metric.mem_ball,dist_eq_norm] using hb,by dsimp; linarith⟩,by dsimp; linarith⟩⟩)
    exact ⟨l,⟨hlS,hrU hl.1.1⟩,hl.1.2,hl.2⟩
  · obtain ⟨u,huS,hu⟩ := hS.exists_mem_open
      ((isOpen_ball.inter (isOpen_lt continuous_const continuous_fst)).inter
        (isOpen_lt continuous_const continuous_snd))
      (show ((ball p r ∩ {x : Point | p.1 < x.1}) ∩ {x : Point | p.2 < x.2}).Nonempty from
        ⟨p+(r/2,r/2),⟨⟨by simpa [Metric.mem_ball,dist_eq_norm] using hb,by dsimp; linarith⟩,by dsimp; linarith⟩⟩)
    exact ⟨u,⟨huS,hrU hu.1.1⟩,hu.1.2,hu.2⟩

lemma monotone_eventually_uniform_approx {f : ℕ → Point → ℝ} {G g : Point → ℝ}
    (hf : ∀ n, Monotone (f n)) {S : Set Point} (hS : Dense S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (G x)))
    (hg : Continuous g) {K U : Set Point} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε)
    (happrox : ∀ x ∈ U, dist (G x) (g x) < ε/4) :
    ∀ᶠ n in atTop, ∀ x ∈ K, dist (f n x) (g x) < ε := by
  have he : ∀ᶠ q : ℕ × Point in atTop ×ˢ 𝓝ˢ K, dist (f q.1 q.2) (g q.2) < ε := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro p hp
    let V := U ∩ {x | dist (g x) (g p) < ε/4}
    have hV : V ∈ 𝓝 p := inter_mem (hU.mem_nhds (hKU hp))
      ((hg.tendsto p).eventually (Metric.ball_mem_nhds _ (by positivity)))
    obtain ⟨⟨l,hl,hlp⟩,⟨u,hu,hpu⟩⟩ := dense_strict_brackets hS hV
    have hll := (hlim l hl.1).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))
    have hlu := (hlim u hu.1).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))
    have hne : ∀ᶠ x in 𝓝 p, l.1 < x.1 ∧ l.2 < x.2 ∧ x.1 < u.1 ∧ x.2 < u.2 ∧
        dist (g x) (g p) < ε/4 := by
      filter_upwards [(continuous_fst.tendsto p).eventually (Ioi_mem_nhds hlp.1),
        (continuous_snd.tendsto p).eventually (Ioi_mem_nhds hlp.2),
        (continuous_fst.tendsto p).eventually (Iio_mem_nhds hpu.1),
        (continuous_snd.tendsto p).eventually (Iio_mem_nhds hpu.2),
        (hg.tendsto p).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))]
        with x hx1 hx2 hx3 hx4 hx5
      exact ⟨hx1,hx2,hx3,hx4,hx5⟩
    filter_upwards [(hll.and hlu).prod_mk hne] with q hq
    rcases hq with ⟨⟨hnl,hnu⟩,hx1,hx2,hx3,hx4,hxg⟩
    have hlo := hf q.1 (show l ≤ q.2 from ⟨hx1.le,hx2.le⟩)
    have hup := hf q.1 (show q.2 ≤ u from ⟨hx3.le,hx4.le⟩)
    have hdl := happrox l hl.2.1
    have hdu := happrox u hu.2.1
    have hlg : dist (g l) (g p) < ε/4 := hl.2.2
    have hug : dist (g u) (g p) < ε/4 := hu.2.2
    rw [Real.dist_eq,abs_lt] at hnl hnu
    rw [Real.dist_eq,abs_lt] at hdl hdu hlg hug hxg
    change dist (f q.1 q.2) (g q.2) < ε
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hen := he.curry
  exact hen.mono fun _ hn => hn.self_of_nhdsSet

lemma firstOrder_eventually_uniform {f : ℕ → Point → ℝ} {G : Point → ℝ}
    (hf : ∀ n, Monotone (f n)) {S : Set Point} (hS : Dense S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (G x)))
    {p : Point} {D : Point →L[ℝ] ℝ} (hd : HasFDerivAt G D p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
        dist (f n x) (G p + D (x-p)) < ε*h := by
  let η := ε/(8*(R+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have he := hd.isLittleO.def hη
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/(R+1),div_pos hr (by positivity),?_⟩
  intro h hh hhr
  have hhr' : (R+1)*h < r := by
    have ht := (lt_div_iff₀ (show 0 < R+1 by positivity)).mp hhr
    nlinarith only [ht]
  apply monotone_eventually_uniform_approx hf hS hlim
    (continuous_const.add (D.continuous.comp (continuous_id.sub continuous_const)))
    (isCompact_closedBall p (R*h)) isOpen_ball (U:=ball p ((R+1)*h))
    (ε:=ε*h)
  · intro x hx
    exact (Metric.mem_closedBall.mp hx).trans_lt (by nlinarith only [hh])
  · exact mul_pos hε hh
  · intro x hx
    have hxnorm : ‖x-p‖ < (R+1)*h := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hxb : x ∈ ball p r := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hxnorm.trans hhr'
    have hxlin := hrb hxb
    calc
      dist (G x) (G p + D (x-p)) = ‖G x-G p-D (x-p)‖ := by
        rw [dist_eq_norm, sub_add_eq_sub_sub]
      _ ≤ η*‖x-p‖ := hxlin
      _ < η*((R+1)*h) := mul_lt_mul_of_pos_left hxnorm hη
      _ = ε*h/8 := by
        dsimp [η]
        field_simp
      _ < ε*h/4 := by nlinarith [mul_pos hε hh]

lemma firstOrder_of_joint {f : ℕ → Point → ℝ} {G : Point → ℝ}
    (hf : ∀ n, Monotone (f n))
    (hlim : ∀ p, ContinuousAt G p → Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G p)))
    (hdiff : ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ G p)
    {p : Point} {D : Point →L[ℝ] ℝ} (hd : HasFDerivAt G D p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
        dist (f n x) (G p + D (x-p)) < ε*h := by
  apply firstOrder_eventually_uniform hf
    (Measure.dense_of_ae (μ := volume) (hdiff.mono fun _ hx => hx.continuousAt))
    _ hd hR hε
  intro x hx
  exact (hlim x hx).comp (tendsto_id.prodMk tendsto_const_nhds)

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

def SeparatedBefore (K H : Window) : Prop :=
  (0 : ℝ) < lower K ∧ upper K < lower H ∧ (upper H : ℝ) < 1

lemma Data.exists_positive_windows (L : Data) [IsProbabilityMeasure (L.edge : Measure Labels)]
    (hna : ∀ᵐ z ∂(L.edge : Measure Labels), NullSingletonClass (L.conditional z)) :
    ∃ K H : Window, SeparatedBefore K H ∧
      (L.edge : Measure Labels) {z | L.conditional z (carrier K) ≠ 0 ∧
        L.conditional z (carrier H) ≠ 0} ≠ 0 := by
  by_contra hn
  have hz : ∀ K H : Window, SeparatedBefore K H →
      (L.edge : Measure Labels) {z | L.conditional z (carrier K) ≠ 0 ∧
        L.conditional z (carrier H) ≠ 0} = 0 := by
    simpa only [not_exists, not_and, not_not] using hn
  have he : ∀ᵐ z ∂(L.edge : Measure Labels), ∀ K H : Window, SeparatedBefore K H →
      ¬(L.conditional z (carrier K) ≠ 0 ∧ L.conditional z (carrier H) ≠ 0) := by
    rw [ae_all_iff]
    intro K
    rw [ae_all_iff]
    intro H
    by_cases hs : SeparatedBefore K H
    · exact (ae_iff.mpr (by simpa only [not_not] using hz K H hs)).mono fun _ hh _ => hh
    · exact Filter.Eventually.of_forall fun _ hh => (hs hh).elim
  obtain ⟨z,hz,hzna⟩ := (he.and hna).exists
  let := hzna
  obtain ⟨K,H,hK,hKH,hH,hk,hh⟩ := exists_separated_positive (L.conditional z)
  exact hz K H ⟨hK,hKH,hH⟩ ⟨hk,hh⟩

theorem Converges.positive_part {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) :
    ∃ (K H A B : Window) (T : Set Labels), SeparatedBefore K H ∧
      carrier A ⊆ carrier H ∧ carrier B ⊆ carrier H ∧ Before A B ∧
      MeasurableSet T ∧ (L.edge : Measure Labels) T ≠ 0 ∧
      (∀ z ∈ T, L.conditional z (carrier K) ≠ 0 ∧ L.conditional z (carrier H) ≠ 0) ∧
      (L.edge : Measure Labels).restrict T ≪ (L.crossings A B : Measure Labels) ∧
      (L.edge : Measure Labels).restrict T ≪ (L.points : Measure Labels) := by
  let := h.edge_probability
  obtain ⟨K,H,hsep,hpos⟩ := L.exists_positive_windows (h.conditional_nullSingleton E hR hC hcoeff herror)
  let U : Set Labels := {z | L.conditional z (carrier K) ≠ 0 ∧ L.conditional z (carrier H) ≠ 0}
  have hU : MeasurableSet U :=
    ((L.conditional.measurable_coe (measurable_carrier K)) (measurableSet_singleton 0)).compl.inter
      ((L.conditional.measurable_coe (measurable_carrier H)) (measurableSet_singleton 0)).compl
  have hac (J : Window) (hJ : ∀ z ∈ U, L.conditional z (carrier J) ≠ 0) :
      (L.edge : Measure Labels).restrict U ≪ (L.edgeWindow J : Measure Labels) := by
    rw [h.window_withDensity hR J]
    exact restrict_ac_withDensity _ _ (L.conditional.measurable_coe (measurable_carrier J)) hU hJ
  have hacH := (hac H (fun _ hz => hz.2)).trans (h.edge_crossing_ac E hR hC hcoeff herror hshort H)
  obtain ⟨AB,V,hV,hVp,hVac⟩ := positive_single_component
    ((L.edge : Measure Labels).restrict U)
    (fun JH : CrossingPairs H => (L.crossings JH.val.1 JH.val.2 : Measure Labels)) hacH
    (by simpa only [Measure.restrict_apply_univ] using hpos)
  let T := V ∩ U
  have hTeq : ((L.edge : Measure Labels).restrict U).restrict V =
      (L.edge : Measure Labels).restrict T := Measure.restrict_restrict hV
  have hTpos : (L.edge : Measure Labels) T ≠ 0 := by
    simpa only [Measure.restrict_apply hV] using hVp
  have hTpts : (L.edge : Measure Labels).restrict T ≪ (L.points : Measure Labels) := by
    exact (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set _ inter_subset_right)).trans
      ((hac K (fun _ hz => hz.1)).trans (h.window_absolutelyContinuous hC hcoeff herror K))
  rw [hTeq] at hVac
  rcases before_or_before AB.property.2.2 with hAB | hBA
  · exact ⟨K,H,AB.val.1,AB.val.2,T,hsep,AB.property.1,AB.property.2.1,hAB,
      hV.inter hU,hTpos,fun _ hz => hz.2,hVac,hTpts⟩
  · rw [h.crossings_comm] at hVac
    exact ⟨K,H,AB.val.2,AB.val.1,T,hsep,AB.property.2.1,AB.property.1,hBA,
      hV.inter hU,hTpos,fun _ hz => hz.2,hVac,hTpts⟩

end PlanarHalving.RankLimits

end OAI
