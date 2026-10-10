import OAI.Geometry.PlaneColoring.Rigidity
import OAI.Geometry.PlaneColoring.States

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma support_good_sequence {A : Set ℝ} {P : ℝ → Prop} {a : ℝ}
    (ha : a∈(volume.restrict A).support) (hP : ∀ᵐt∂volume,t∈A → P t) :
    ∃t : ℕ → ℝ, Tendsto t atTop (𝓝 a) ∧ ∀n,P (t n) := by
  have hex (n : ℕ) : ∃t,dist t a<1/((n:ℝ)+1) ∧ P t := by
    have hp : 0<volume (Metric.ball a (1/((n:ℝ)+1))∩A) := by
      simpa only [Measure.restrict_apply measurableSet_ball] using
        (Measure.mem_support_iff_forall a).mp ha _ (Metric.ball_mem_nhds a (by positivity))
    obtain ⟨t,ht,hpt⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually hP).exists
    exact ⟨t,ht.1,hpt ht.2⟩
  choose t hd hpt using hex
  refine ⟨t,?_,hpt⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hd n).le) tendsto_one_div_add_atTop_nhds_zero_nat
lemma state_support_avoiding_trace (hw : WeakColoring k c) {x : ℂ} {A : Set ℝ} {J : Finset (Fin k)}
    (hA : RealState hc x A J) {a : ℝ} (ha : a∈(volume.restrict A).support) :
    ∃b : TraceVector k,IsTrace c hc (x+direction (a : Angles)) b ∧ ∀i∈J,traceValue b i=0 := by
  have he := angleMk_quasiMeasurePreserving.ae (ae_circle_palette_exclusion c hc hw x)
  have ht := angleMk_quasiMeasurePreserving.ae (ae_circle_typicalSampling c hc x)
  have hp : ∀ᵐt : ℝ∂volume,t∈A → TypicalSampling c (x+direction (t : Angles)) 1 ∧
      ∀i∈J,sample c hc (x+direction (t : Angles)) 1 i=0 := by
    filter_upwards [he,ht,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun hi : i∈J => hA.2 i hi))] with t he ht hJ hta
    refine ⟨ht,?_⟩
    intro i hi
    apply Lp.ext
    filter_upwards [sample_ae c hc (x+direction (t : Angles)) 1 i,he,Lp.coeFn_zero ℝ 2 angularMeasure] with v hv he hz
    rw [hz,hv]
    have hne : c (x+direction (t : Angles)+direction v)≠i := by
      intro hh
      apply he
      rw [hh]
      exact (mem_palette c hc x (t : Angles) i).mpr (hJ i hi hta)
    simp only [sampleFn,Complex.ofReal_one,one_mul,ite_eq_right hne,Pi.zero_apply]
  obtain ⟨t,ht,hp⟩ := support_good_sequence ha hp
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (x+direction (t n : Angles)) 1)))
  have hlim : Tendsto (fun n => x+direction (t n : Angles)) atTop (𝓝 (x+direction (a : Angles))) :=
    tendsto_const_nhds.add (direction_continuous.continuousAt.tendsto.comp ((AddCircle.continuous_mk' (2*Real.pi)).continuousAt.tendsto.comp ht))
  refine ⟨b,trace_of_realization c hc (fun n => (hp (φ n)).1) (hlim.comp hφ.tendsto_atTop) tendsto_const_nhds hb,?_⟩
  intro i hi
  have hh := traceCode_tendsto_iff.mp hb i (traceValue b i)
  simp only [Function.comp_apply,traceValue_sampleCode,(hp _).2 i hi,inner_zero_left] at hh
  exact inner_self_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh).symm
lemma avoiding_trace_palette {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b)
    {J : Finset (Fin k)} (hJ : ∀i∈J,traceValue b i=0) :
    ∀ᵐt∂angularMeasure,¬palette c hc x t⊆J := by
  have hs : (fun t => ∑i,traceValue b i t)=ᵐ[angularMeasure](fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc hb).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  have hz (i : Fin k) : ∀ᵐt∂angularMeasure,i∈J → traceValue b i t=0 := by
    by_cases hi : i∈J
    · rw [hJ i hi]
      exact (Lp.coeFn_zero ℝ 2 angularMeasure).mono fun _ hh _ => hh
    · exact Eventually.of_forall fun _ hh => (hi hh).elim
  filter_upwards [hs,ae_all_iff.mpr hz,ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i ⟨b,hb⟩)] with t hs hz hp hsub
  have hn : ∀i : Fin k,traceValue b i t≤0 := by
    intro i
    by_contra! hpos
    have hm := hsub ((mem_palette c hc x t i).mpr (hp i hpos))
    linarith [hz i hm]
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn i)
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma sample_region_ae (r : ℝ) {W : Set ℂ} {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) :
    ∀ᵐy : ℂ∂volume,∀ᵐt∂angularMeasure,y+(r : ℂ)*direction t∈W →
      c (y+(r : ℂ)*direction t)∈J := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hW)
include hc in
lemma sampling_near_region {x : ℂ} {r : ℝ} (hr : 0<r) {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hmem : ∀t∈K,x+(r : ℂ)*direction t∈W) {δ : ℝ} (hδ : 0<δ) :
    ∃y : ℂ,dist y x<δ ∧ TypicalSampling c y r ∧
      ∀ᵐt∂angularMeasure,t∈K → c (y+(r : ℂ)*direction t)∈J := by
  let U : Set (ℂ × Angles) := {p | p.1+(r : ℂ)*direction p.2∈W}
  have hU : IsOpen U := ho.preimage (continuous_fst.add (continuous_const.mul (direction_continuous.comp continuous_snd)))
  obtain ⟨V,T,hV,_,hxV,hKT,hVT⟩ := generalized_tube_lemma (isCompact_singleton (x := x)) hK hU
    (by rintro ⟨y,t⟩ ⟨hy,ht⟩; change y=x at hy; subst y; exact hmem t ht)
  have hv : x∈V := hxV (mem_singleton x)
  have hpos : 0<volume (V∩Metric.ball x δ) := (hV.inter Metric.isOpen_ball).measure_pos volume
    ⟨x,hv,Metric.mem_ball_self hδ⟩
  obtain ⟨y,hy,hyp,hyW⟩ := ((frequently_ae_mem_iff.mpr hpos.ne').and_eventually
    ((ae_typicalSampling c hc hr).and (sample_region_ae c r hW))).exists
  refine ⟨y,hy.2,hyp,hyW.mono fun t ht htK => ht ?_⟩
  exact hVT (show (y,t)∈V×ˢT from ⟨hy.1,hKT htK⟩)
lemma weak_limit_zero_on {f : ℕ → RealL2 angularMeasure} {b : RealL2 angularMeasure}
    {K : Set Angles} (hK : MeasurableSet K)
    (ht : ∀v,Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hb : 0≤ᵐ[angularMeasure] b)
    (hf : ∀n,∀ᵐt∂angularMeasure,t∈K → f n t=0) :
    ∀ᵐt∂angularMeasure,t∈K → b t=0 := by
  have ht' := ht (indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1)
  have he (v : RealL2 angularMeasure) :
      ⟪v,indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1⟫=∫t in K,v t∂angularMeasure := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp only [he] at ht'
  have hf0 (n) : ∫t in K,f n t∂angularMeasure=0 := by
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff' hK).mpr (hf n)
  simp only [hf0] at ht'
  have hzero : ∫t in K,b t∂angularMeasure=0 := (tendsto_nhds_unique tendsto_const_nhds ht').symm
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hb)
    ((Lp.memLp b).integrable (by norm_num)).integrableOn).mp hzero
  exact (ae_restrict_iff' hK).mp hz
lemma trace_region_palette {x : ℂ} {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) {r : ℕ → ℝ}
    (hr : ∀n,0<r n) (hrt : Tendsto r atTop (𝓝 1))
    (hmem : ∀n,∀t∈K,x+(r n : ℂ)*direction t∈W) :
    ∀ᵐt∂angularMeasure,t∈K → (palette c hc x t∩J).Nonempty := by
  have hex (n : ℕ) := sampling_near_region c hc (hr n) hK ho hW (hmem n)
    (δ := 1/((n:ℝ)+1)) (by positivity)
  choose y hy hyt hyJ using hex
  have hyl : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hy n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (y n) (r n))))
  have htrace := trace_of_realization c hc (fun n => hyt (φ n)) (hyl.comp hφ.tendsto_atTop)
    (hrt.comp hφ.tendsto_atTop) hb
  have hz (i : Fin k) (hi : i∉J) : ∀ᵐt∂angularMeasure,t∈K → traceValue b i t=0 := by
    apply weak_limit_zero_on hK.measurableSet
      (by simpa only [traceValue_sampleCode] using traceCode_tendsto_iff.mp hb i)
      ((trace_bounds c hc htrace).1 i)
    intro n
    filter_upwards [hyJ (φ n),sample_ae c hc (y (φ n)) (r (φ n)) i] with t ht he htK
    simp only [Function.comp_apply,traceValue_sampleCode]
    rw [he]
    unfold sampleFn
    split_ifs with htcol
    · exact (hi (htcol ▸ ht htK)).elim
    · rfl
  have hs : (fun t => ∑i,traceValue b i t)=ᵐ[angularMeasure](fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc htrace).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [hs,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hz i)),
    ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i ⟨b,htrace⟩)] with t hs hz hp htK
  by_contra! hn
  have hn' : ∀i,traceValue b i t≤0 := by
    intro i
    by_contra! hpos
    have hi : i∈palette c hc x t := (mem_palette c hc x t i).mpr (hp i hpos)
    by_cases hiJ : i∈J
    · have hh := Finset.mem_inter.mpr ⟨hi,hiJ⟩
      rw [hn] at hh
      exact Finset.notMem_empty i hh
    · linarith [hz i hiJ htK]
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn' i)
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma outer_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      1<r → r<1+δ → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let r : ℕ → ℝ := fun n => 1+(δ/2)/(n+1)
  have hr (n) : 0<r n := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith)
    · dsimp [r]
      have : 0<(δ/2)/((n:ℝ)+1) := by positivity
      linarith
    · have hn : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hb := div_le_self (by positivity : (0:ℝ)≤δ/2) hn
      dsimp [r]
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
lemma inner_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      0<r → 1-δ<r → r<1 → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let ε := min δ (1/2)
  have he : 0<ε := lt_min hδ (by norm_num)
  have heδ : ε≤δ := min_le_left _ _
  have he1 : ε≤1/2 := min_le_right _ _
  let r : ℕ → ℝ := fun n => 1-(ε/2)/(n+1)
  have hb (n : ℕ) : (ε/2)/(n+1)≤ε/2 := div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr (n) : 0<r n := by dsimp [r]; linarith [hb n]
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith) (r n) (hr n)
    · dsimp [r]; linarith [hb n]
    · dsimp [r]
      have : 0<(ε/2)/((n:ℝ)+1) := by positivity
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- The source local binary rigidity on arbitrary one-sided strips, allowing
independent choices of radial side at the two equilateral neighbors. -/
lemma binary_strip_rigidity {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {a b : Fin k} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : ∀ᵐq : ℂ∂volume,q∈U → c q=a ∨ c q=b)
    (hVc : ∀ᵐq : ℂ∂volume,q∈V → c q=a ∨ c q=b)
    {x e : ℂ} (he : ‖e‖=1) {δ : ℝ} (hδ : 0<δ) (bu bv : Bool)
    (hstripU : ∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if bu then 1<r else r<1) → x+(r:ℂ)*e'∈U)
    (hstripV : ∀e' : ℂ,‖e'‖=1 → dist e' (e*(Circle.exp (Real.pi/3) : ℂ))<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if bv then 1<r else r<1) → x+(r:ℂ)*e'∈V) :
    ∃i : Fin k,(i=a ∨ i=b) ∧ ∃η>0,∀e' : ℂ,‖e'‖=1 → dist e' e<η → ∀r : ℝ,
      0<r → |r-1|<η → (if bu then 1<r else r<1) → x+(r:ℂ)*e'∈essentialLocalSet c i := by
  obtain ⟨v,hv,hpv⟩ := radial_unit_contact he hδ bv hstripV
  obtain ⟨w,hpw,hw',hd⟩ := open_two_unit_directions hV hv hpv
  let W : Set ℂ := {p | p+v∈V ∧ p+w∈V}
  have hW : IsOpen W := (hV.preimage (continuous_id.add continuous_const)).inter
    (hV.preimage (continuous_id.add continuous_const))
  obtain ⟨ε,hε,hbox⟩ := polarBox_small hδ hW ⟨hpv,hpw⟩ hstripU he
  obtain ⟨i,hi,_⟩ := connected_local_ae_constant (polarBox_connected x e bu hε) (fun p hp => by
    have hp' := hbox hp
    obtain ⟨r,hr,j,hj⟩ := binary_open_local_rigidity hc hw hU hV hUc hVc hp'.1 hp'.2.1 hp'.2.2 hv hw' hd
    exact ⟨j,Metric.ball p r,Metric.isOpen_ball,Metric.mem_ball_self hr,hj⟩)
  have hab : i=a ∨ i=b := by
    obtain ⟨p,hp⟩ := (polarBox_connected x e bu hε).nonempty
    have hpos := (hU.inter (essentialLocalSet_open c i)).measure_pos (volume : Measure ℂ)
      ⟨p,(hbox hp).1,hi hp⟩
    obtain ⟨q,hq,hqa⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
      (ae_restrict_of_ae (hUc.and (essentialLocalSet_ae c i)))
    simpa only [hqa.2 hq.2] using hqa.1 hq.1
  obtain ⟨η,hη,hh⟩ := polarBox_contains_strip he bu hε
  exact ⟨i,hab,η,hη,fun e' he' hh' r _ hr hside => hi (hh e' he' hh' r hr hside)⟩
/-- The resulting fixed outsider is actually in the maximal palette on an
angular neighborhood, by one-sided radial weak traces. -/
lemma binary_strip_palette_rigidity {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    {a b : Fin k} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : ∀ᵐq : ℂ∂volume,q∈U → c q=a ∨ c q=b)
    (hVc : ∀ᵐq : ℂ∂volume,q∈V → c q=a ∨ c q=b)
    {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ) (bu bv : Bool)
    (hstripU : ∀e' : ℂ,‖e'‖=1 → dist e' (direction t)<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if bu then 1<r else r<1) → x+(r:ℂ)*e'∈U)
    (hstripV : ∀e' : ℂ,‖e'‖=1 → dist e' (direction t*(Circle.exp (Real.pi/3) : ℂ))<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if bv then 1<r else r<1) → x+(r:ℂ)*e'∈V) :
    ∃i : Fin k,(i=a ∨ i=b) ∧ ∃A : Set Angles,IsOpen A ∧ t∈A ∧
      ∀ᵐu∂angularMeasure,u∈A → i∈palette c hc x u := by
  obtain ⟨i,hi,η,hη,hs⟩ := binary_strip_rigidity hc hw hU hV hUc hVc (direction_norm t) hδ bu bv hstripU hstripV
  have hmono : ∀ᵐq : ℂ∂volume,q∈essentialLocalSet c i → c q∈({i} : Finset (Fin k)) :=
    (essentialLocalSet_ae c i).mono fun q hq hqi => by simpa only [Finset.mem_singleton] using hq hqi
  have hex : ∃A : Set Angles,IsOpen A ∧ t∈A ∧
      ∀ᵐu∂angularMeasure,u∈A → (palette c hc x u∩{i}).Nonempty := by
    cases bu
    · apply inner_strip_trace c hc hη (essentialLocalSet_open c i) hmono
      intro u hu r hr hrη hr1
      apply hs (direction u) (direction_norm u) hu r hr _ hr1
      rw [abs_lt]; constructor <;> linarith
    · apply outer_strip_trace c hc hη (essentialLocalSet_open c i) hmono
      intro u hu r hr1 hrη
      apply hs (direction u) (direction_norm u) hu r (by linarith) _ hr1
      rw [abs_lt]; constructor <;> linarith
  obtain ⟨A,hA,ht,hae⟩ := hex
  refine ⟨i,hi,A,hA,ht,hae.mono fun u hu hAu => ?_⟩
  obtain ⟨j,hj⟩ := hu hAu
  rcases Finset.mem_inter.mp hj with ⟨hjp,hji⟩
  simpa only [Finset.mem_singleton.mp hji] using hjp
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
/-- If two unit rays can never be simultaneously positive at a generic angle,
they are antipodal. This avoids any assumption about multiplicities of ray lines. -/
lemma unit_antipodes_of_no_positive {v w : ℂ} (hv : ‖v‖=1) (hw : ‖w‖=1)
    (h : ∀ᵐt∂angularMeasure,¬(0<⟪direction t,v⟫ ∧ 0<⟪direction t,w⟫)) : w= -v := by
  by_contra hne
  have hsum : v+w≠0 := by
    intro hz
    apply hne
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hz
  have hvv : ⟪v,v⟫=(1:ℝ) := by rw [real_inner_self_eq_norm_sq,hv]; norm_num
  have hww : ⟪w,w⟫=(1:ℝ) := by rw [real_inner_self_eq_norm_sq,hw]; norm_num
  have hs : 0<⟪v+w,v+w⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hsum)
  have hc := real_inner_comm v w
  simp only [inner_add_left,inner_add_right,hvv,hww] at hs
  have hvpos : 0<⟪v+w,v⟫ := by rw [inner_add_left,hvv]; linarith
  have hwpos : 0<⟪v+w,w⟫ := by rw [inner_add_left,hww]; linarith
  let e : ℂ := ‖v+w‖⁻¹ • (v+w)
  have he : ‖e‖=1 := by
    simp only [e,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg (v+w))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hsum)
  have hev : 0<⟪e,v⟫ := by
    change 0<⟪‖v+w‖⁻¹ • (v+w),_⟫
    rw [real_inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hsum)) hvpos
  have hew : 0<⟪e,w⟫ := by
    change 0<⟪‖v+w‖⁻¹ • (v+w),_⟫
    rw [real_inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hsum)) hwpos
  obtain ⟨t,ht⟩ := direction_exists he
  let U : Set Angles := {t | 0<⟪direction t,v⟫ ∧ 0<⟪direction t,w⟫}
  have hUv : IsOpen {t : Angles | 0<⟪direction t,v⟫} := isOpen_lt continuous_const (direction_continuous.inner continuous_const)
  have hUw : IsOpen {t : Angles | 0<⟪direction t,w⟫} := isOpen_lt continuous_const (direction_continuous.inner continuous_const)
  have hU : IsOpen U := hUv.inter hUw
  have htU : t∈U := by change _∧_; rw [ht]; exact ⟨hev,hew⟩
  have hpos := hU.measure_pos angularMeasure ⟨t,htU⟩
  obtain ⟨u,hu,hu'⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae h)
  exact hu' hu
/-- The source's all-generic split condition already forces opposite edge
positions to be actual antipodes; the collinear case is retained. -/
lemma four_split_antipodes (v : Fin 4 → ℂ) (hv : ∀i,‖v i‖=1)
    (hsplit : ∀ᵐt∂angularMeasure,∀i,¬(0<⟪direction t,v i⟫ ∧ 0<⟪direction t,v (i+2)⟫)) :
    ∀i,v (i+2)= -v i := by
  intro i
  exact unit_antipodes_of_no_positive (hv i) (hv (i+2)) (hsplit.mono fun _ ht => ht i)
end EuclideanFiveColor
end

end OAI
