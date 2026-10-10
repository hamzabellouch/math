import OAI.Probability.FKMaps.GHPBounds

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The positive source normalization in original edge units. -/
def crtScale (P : Parameters) : ℝ := (actualOffspring P).sigma/(2*Real.sqrt 2*metricMean P)
lemma crtScale_pos (P : Parameters) : 0<crtScale P :=
  div_pos (actualOffspring P).sigma_pos (by have h := metricMean_pos P; positivity)

def edgeScale (P : Parameters) (n : ℕ) : ℝ := crtScale P/Real.sqrt ((n:ℝ)+1)
lemma edgeScale_pos (P : Parameters) (n : ℕ) : 0<edgeScale P n :=
  div_pos (crtScale_pos P) (Real.sqrt_pos.mpr (by positivity))

def heightFactor (n : ℕ) : ℝ := Real.sqrt (1+1/(2*((n:ℝ)+1)))
lemma heightFactor_pos (n : ℕ) : 0<heightFactor n := Real.sqrt_pos.mpr (by positivity)
lemma heightFactor_tendsto : Tendsto heightFactor atTop (𝓝 1) := by
  have hh : Tendsto (fun n : ℕ => 1/(2*((n:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num))
  have hs := ((tendsto_const_nhds.add hh (a := (1:ℝ))).sqrt)
  change Tendsto (fun n : ℕ => Real.sqrt (1+1/(2*((n:ℝ)+1)))) atTop (𝓝 1)
  simpa only [add_zero,Real.sqrt_one] using hs

lemma sqrt_size_ratio (n : ℕ) :
    Real.sqrt ((2*(n+1)+1:ℕ):ℝ)=heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1) := by
  have hn : 0 ≤ (n:ℝ)+1 := by positivity
  have hh : 0 ≤ 1+1/(2*((n:ℝ)+1)) := by positivity
  have h₁ := Real.sq_sqrt (show 0 ≤ ((2*(n+1)+1:ℕ):ℝ) by positivity)
  have h₂ := Real.sq_sqrt hh
  have h₃ := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h₄ := Real.sq_sqrt hn
  have he : (heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1))^2=((2*(n+1)+1:ℕ):ℝ) := by
    rw [mul_pow,mul_pow,h₃,h₄]
    change (Real.sqrt (1+1/(2*((n:ℝ)+1))))^2*2*((n:ℝ)+1)=_
    rw [h₂]
    push_cast
    field_simp
  nlinarith [Real.sqrt_nonneg ((2*(n+1)+1:ℕ):ℝ),show 0 ≤ heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1) by
    exact mul_nonneg (mul_nonneg (heightFactor_pos n).le (Real.sqrt_nonneg 2)) (Real.sqrt_nonneg _)]

lemma edgeScale_heightFactor (P : Parameters) (n : ℕ) :
    edgeScale P n*metricMean P*2*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)/(actualOffspring P).sigma=heightFactor n := by
  rw [sqrt_size_ratio]
  have hσ := (actualOffspring P).sigma_pos
  have hβ := metricMean_pos P
  have h₂ : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hn : 0<Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  unfold edgeScale crtScale
  field_simp

lemma edgeScale_sqrt_size_tendsto (P : Parameters) :
    Tendsto (fun n => edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)) atTop
      (𝓝 ((actualOffspring P).sigma/(2*metricMean P))) := by
  have he (n : ℕ) : edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)=
      heightFactor n*((actualOffspring P).sigma/(2*metricMean P)) := by
    have h := edgeScale_heightFactor P n
    have hσ := (actualOffspring P).sigma_pos
    have hβ := metricMean_pos P
    field_simp at h ⊢
    nlinarith
  simp_rw [he]
  simpa only [one_mul] using heightFactor_tendsto.mul_const ((actualOffspring P).sigma/(2*metricMean P))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma distribution_smul_one {E Ω' : Type*} {Ω : ℕ → Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ ν)
    (hm : ∀ n,Measurable (X n)) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1)) :
    TendstoInDistribution (fun n x => a n • X n x) atTop Z μ ν := by
  apply tendstoInDistribution_of_close h (fun n => ((hm n).const_smul (a n)).aemeasurable)
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨C,hC,hbound⟩ := distribution_norm_tight h hm (half_pos hη)
  have ha' : Tendsto (fun n => |1-a n|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (tendsto_const_nhds.sub ha (a := (1:ℝ))).abs
  filter_upwards [hbound,ha'.eventually (gt_mem_nhds (div_pos hε hC))] with n hn hn'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  apply lt_of_le_of_lt _ (half_lt_self hη)
  apply le_trans _ hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  change C<‖X n x‖
  change ε<dist (X n x) (a n • X n x) at hx
  rw [dist_eq_norm,show X n x-a n • X n x=(1-a n) • X n x by rw [sub_smul,one_smul],
    norm_smul,Real.norm_eq_abs] at hx
  by_contra hbad
  have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (abs_nonneg (1-a n))
  have hh' := (lt_div_iff₀ hC).mp hn'
  linarith

lemma CriticalEvenOffspring.markedCodeLaw_map_fst (p : CriticalEvenOffspring)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) :
    (p.markedCodeLaw κ n).map Prod.fst=p.codeLaw n := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_fst hE,← ofReal_measureReal,← ofReal_measureReal]
  exact congrArg ENNReal.ofReal (p.markedCodeLaw_fst κ n E)

local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma CriticalEvenOffspring.marked_height_CLT (p : CriticalEvenOffspring)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    TendstoInDistribution (fun n (x : Code (2*n+1) × (Fin (2*n+1) → A)) => heightCode p x.1)
      atTop (excursionPath B) (p.markedCodeLaw κ) P := by
  have hh := p.heightCode_CLT hB hI
  refine ⟨fun n => ((measurable_of_countable (heightCode p)).comp measurable_fst).aemeasurable,
    hh.aemeasurable_limit,?_⟩
  have hmap (n : ℕ) : (p.markedCodeLaw κ n).map (fun x => heightCode p x.1)=
      (p.codeLaw n).map (heightCode p) := by
    change (p.markedCodeLaw κ n).map (heightCode p ∘ Prod.fst)=_
    rw [← Measure.map_map (measurable_of_countable _) measurable_fst,p.markedCodeLaw_map_fst]
  simpa only [hmap] using hh.tendsto

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

abbrev ActualDraw (n : ℕ) := Code (2*(n+1)+1) × (Fin (2*(n+1)+1) → CoreLabel)
abbrev actualDrawLaw (P : Parameters) (n : ℕ) : Measure (ActualDraw n) :=
  (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1)
def actualHeight (P : Parameters) (n : ℕ) (x : ActualDraw n) : C(unitInterval,ℝ) :=
  heightFactor n • heightCode (actualOffspring P) x.1

/-- The exact original-edge normalization of the same sampled marked tree
has the standard (not rescaled) three-bridge excursion limit. -/
theorem actualHeight_CLT (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ) :
    TendstoInDistribution (actualHeight P) atTop (excursionPath B) (actualDrawLaw P) μ := by
  have hh := (actualOffspring P).marked_height_CLT
    (fun k => (CoreLabel.markLaw P k).toMeasure) hB hI
  have hr : TendstoInDistribution
      (fun n (x : ActualDraw n) => heightCode (actualOffspring P) x.1) atTop
      (excursionPath B) (actualDrawLaw P) μ :=
    ⟨fun n => hh.forall_aemeasurable (n+1),hh.aemeasurable_limit,
      hh.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  exact distribution_smul_one hr (fun _ => measurable_of_countable _) heightFactor_tendsto

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- A compact-cover transfer lemma for varying discrete approximations. The
local hypothesis is deterministic; only the stated error events vanish in
probability. No independent coupling or random-cut independence is used. -/
theorem local_probability_transfer {E Ω' : Type*} {Ω : ℕ → Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ ν)
    (hm : ∀ n,Measurable (X n)) (Y : ∀ n,Ω n → ℝ) (G : E → ℝ)
    (Bad : ∀ n,ℝ → Set (Ω n))
    (hBad : ∀ a,0<a → Tendsto (fun n => (μ n).real (Bad n a)) atTop (𝓝 0))
    (hloc : ∀ ε,0<ε → ∀ f : E,∃ r : ℝ,0<r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,
      ∀ n≥N,∀ x : Ω n,dist (X n x) f<r → x∉Bad n a → |Y n x-G (X n x)| ≤ ε) :
    ∀ ε,0<ε → Tendsto (fun n => (μ n).real {x | ε < |Y n x-G (X n x)|}) atTop (𝓝 0) := by
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  have : IsProbabilityMeasure (ν.map Z) := inferInstance
  obtain ⟨K,hK,hKμ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν.map Z)) (ENNReal.ofReal (η/4)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hKμ' := hKμ (ν.map Z) (Set.mem_singleton _)
  choose r hr a ha N hfit using hloc ε hε
  obtain ⟨S,hSK,hS,hcover⟩ := hK.elim_finite_subcover_image
    (fun f (_ : f∈K) => Metric.isOpen_ball (x := f) (ε := r f)) (by
      intro f hf
      simp only [Set.mem_iUnion]
      exact ⟨f,hf,Metric.mem_ball_self (hr f)⟩)
  let I := hS.toFinset
  let O : Set E := ⋃ f∈I,Metric.ball f (r f)
  have hO : IsOpen O := isOpen_iUnion (fun f => isOpen_iUnion (fun _ => Metric.isOpen_ball))
  have hKO : K⊆O := by simpa only [O,I,Set.Finite.mem_toFinset] using hcover
  have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hO.isClosed_compl
  have hlim : limsup (fun n => (μ n) ((X n) ⁻¹' Oᶜ)) atTop≤ENNReal.ofReal (η/4) := by
    simpa only [ProbabilityMeasure.coe_mk,Measure.map_apply (hm _) hO.measurableSet.compl] using
      hclosed.trans ((measure_mono (Set.compl_subset_compl.mpr hKO)).trans hKμ')
  have hev : ∀ᶠ n in atTop,(μ n).real ((X n) ⁻¹' Oᶜ)<η/2 := by
    have hh : ∀ᶠ n in atTop,(μ n) ((X n) ⁻¹' Oᶜ)<ENNReal.ofReal (η/2) :=
      eventually_lt_of_limsup_lt (hlim.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (half_pos hη)).mpr (by linarith)))
    filter_upwards [hh] with n hn
    rw [← ofReal_measureReal] at hn
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hn
  have hsum : Tendsto (fun n => ∑ f∈I,(μ n).real (Bad n (a f))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I (fun f _ => hBad (a f) (ha f))
  have hN : ∀ᶠ n in atTop,∀ f∈I,N f≤n := by
    exact (eventually_all_finset I).mpr (fun f _ => eventually_ge_atTop (N f))
  filter_upwards [hev,hsum.eventually (gt_mem_nhds (half_pos hη)),hN] with n hn hn' hNn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  have hs : {x | ε < |Y n x-G (X n x)|}⊆(X n) ⁻¹' Oᶜ ∪ ⋃ f∈I,Bad n (a f) := by
    intro x hx
    by_cases hxO : X n x∈O
    · right
      obtain ⟨f,hf,hxf⟩ := Set.mem_iUnion₂.mp hxO
      apply Set.mem_iUnion₂.mpr
      refine ⟨f,hf,?_⟩
      by_contra hbad
      exact not_lt_of_ge (hfit f n (hNn f hf) x hxf hbad) hx
    · exact Or.inl hxO
  have hh := (measureReal_mono (μ := μ n) hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_biUnion_finset_le I (fun f => Bad n (a f)))))
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology NNReal
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The same measured relation compares to a nearby deterministic path;
this avoids presuming a triangle inequality for the presentation distance. -/
theorem marked_nearby_ghp_bound (P : Parameters) (n : ℕ)
    (x : MarkedCode (2*(n+1)+1)) (f : C(unitInterval,ℝ)) (a r η δ : ℝ) (hδ : 0<δ)
    (herr : ∀ j : Fin (2*(n+1)+1),
      |markedSpineSum coreIncrement x.val.1 j.isLt.le x.val.2-metricMean P*height x.val.1.val j.val| ≤
        a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ))
    (hprox : dist (actualHeight P n x.val) f ≤ r)
    (hmod : ∀ s u,dist s u ≤ 1/(2*((n:ℝ)+1)) → |f s-f u| ≤ η)
    (hsmall : 4*edgeScale P n*((ofMarkedCode x).maxDegree:ℝ)+
      4*(edgeScale P n*a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)+r)+4*η ≤ 2*δ) :
    FKCRT.ghpEDist (FKCRT.treeSpace f)
      (FKCRT.mapSpace (edgeScale P n) ((FKCRT.rootedWordEquiv n).symm
        ((successfulMarkedEquiv n).symm x)).1) ≤ ENNReal.ofReal δ := by
  let t := ofMarkedCode x
  have hsize := ofMarkedCode_size x
  have hw := ofMarkedCode_word_successful n x
  have hlen : t.word.length=2*(n+1) := by rw [hw,List.length_ofFn]
  have he : ∀ v : t.Node,|(t.routeLength v:ℝ)-metricMean P*t.depth v| ≤ a*Real.sqrt t.labels.length := by
    rw [hsize]
    exact marked_route_error x _ _ herr
  have hpath : ((edgeScale P n*metricMean P*2*Real.sqrt t.labels.length/(actualOffspring P).sigma) •
      heightCode (actualOffspring P) t.toCode)=actualHeight P n x.val := by
    simp only [t,hsize,marked_heightCode,edgeScale_heightFactor,actualHeight]
  have hfit := t.route_heightCode_fit (actualOffspring P) (metricMean P) (edgeScale P n) a
    (edgeScale_pos P n).le he
  rw [hpath] at hfit
  have hb : ∀ v : t.Node,|edgeScale P n*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤
      edgeScale P n*a*Real.sqrt t.labels.length+r := by
    intro v
    have hp := (ContinuousMap.dist_apply_le_dist (f := actualHeight P n x.val) (g := f) (t.nodePoint v)).trans hprox
    rw [Real.dist_eq] at hp
    exact (abs_sub_le _ _ _).trans (add_le_add (hfit v) hp)
  obtain ⟨e,he',hp⟩ := t.realized_intertwine _ hw
  apply t.ghp_tree_map_bound _ e (by omega) he' hp hlen f (edgeScale_pos P n) hδ hb
  · intro s u hsu
    apply hmod s u
    simpa only [hlen,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hsu
  · simpa only [t,hsize] using hsmall

end FKCRT.Inventory.CoreTree
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- All and only the three exceptional events needed for the original map
comparison: impossible marks (a null set), a macroscopic core, and a large
uniform ancestral distance error. -/
def metricBad (P : Parameters) (n : ℕ) (a : ℝ) : Set (ActualDraw n) :=
  {x | ¬∀ i,(x.2 i).arity=(x.1.val i).val} ∪
  {x | ∃ h : ∀ i,(x.2 i).arity=(x.1.val i).val,
    a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)<((CoreTree.ofMarkedCode ⟨x,h⟩).maxDegree:ℝ)} ∪
  {x | ∃ j : Fin (2*(n+1)+1),a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) <
    |markedSpineSum coreIncrement x.1 j.isLt.le x.2-metricMean P*height x.1.val j.val|}

lemma metricBad_limit (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun n => (actualDrawLaw P n).real (metricBad P n a)) atTop (𝓝 0) := by
  have hcore := (actual_max_core P ha).comp (tendsto_add_atTop_nat 1)
  have herr := (actual_uniform_metric_spine P hB ha).comp (tendsto_add_atTop_nat 1)
  have ht := hcore.add herr
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  have hc : (actualDrawLaw P n).real {x | ¬∀ i,(x.2 i).arity=(x.1.val i).val}=0 := by
    unfold Measure.real
    rw [ae_iff.mp (actual_marked_compatible P (n+1)),ENNReal.toReal_zero]
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ le_rfl
  apply (measureReal_union_le _ _).trans
  rw [hc,zero_add]
  exact le_rfl

/-- Local deterministic stability at every continuous limit path. This is
the missing compact-cover interface, with the original map, exact degree
mass, positive source normalization, and true bad events. -/
theorem metric_test_local (P : Parameters) (F : FKCRT.MetricMeasureData → ℝ)
    (hF : FKCRT.IsGHPTest F) (ε : ℝ) (hε : 0<ε) (f : C(unitInterval,ℝ)) :
    ∃ r : ℝ,0<r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,∀ n≥N,∀ x : ActualDraw n,
      dist (actualHeight P n x) f<r → x∉metricBad P n a →
      |FKCRT.markedMapTest (edgeScale P n) n F x-F (FKCRT.treeSpace (actualHeight P n x))| ≤ ε := by
  obtain ⟨δ,hδ,hcont⟩ := hF.2 (FKCRT.treeSpace f) (FKCRT.treeSpace_valid f.continuous) (ε/2) (half_pos hε)
  obtain ⟨r₀,hr₀,hG⟩ := Metric.continuousAt_iff.mp (hF.continuous_treeSpace.continuousAt (x := f)) (ε/2) (half_pos hε)
  let L := (actualOffspring P).sigma/(2*metricMean P)+1
  have hL : 0<L := by dsimp [L];have hβ := metricMean_pos P;have hσ := (actualOffspring P).sigma_pos; positivity
  let r := min r₀ (δ/16)
  let a := δ/(32*(L+1))
  have hr : 0<r := lt_min hr₀ (by positivity)
  have ha : 0<a := by dsimp [a];positivity
  have hLbound : ∀ᶠ n in atTop,edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) ≤ L := by
    exact ((edgeScale_sqrt_size_tendsto P).eventually (gt_mem_nhds (by dsimp [L];linarith))).mono (fun _ h => h.le)
  obtain ⟨ζ,hζ,hmod⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) (δ/16) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => 1/(2*((n:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hLbound.and (hmesh.eventually (gt_mem_nhds hζ)))
  refine ⟨r,hr,a,ha,N,?_⟩
  intro n hn x hx hbad
  have hcompat : ∀ i,(x.2 i).arity=(x.1.val i).val := by
    by_contra hc
    exact hbad (Or.inl (Or.inl hc))
  let y : CoreTree.MarkedCode (2*(n+1)+1) := ⟨x,hcompat⟩
  have hcore : ((CoreTree.ofMarkedCode y).maxDegree:ℝ) ≤ a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) := by
    by_contra hc
    exact hbad (Or.inl (Or.inr ⟨hcompat,lt_of_not_ge hc⟩))
  have herr : ∀ j : Fin (2*(n+1)+1),|markedSpineSum coreIncrement x.1 j.isLt.le x.2-
      metricMean P*height x.1.val j.val| ≤ a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) := by
    intro j
    by_contra hc
    exact hbad (Or.inr ⟨j,lt_of_not_ge hc⟩)
  have hghp := CoreTree.marked_nearby_ghp_bound P n y f a r (δ/16) (δ/2) (half_pos hδ) herr hx.le
    (fun s u hsu => by
      have hh := hmod (hsu.trans_lt (hN n hn).2)
      simpa only [Real.dist_eq] using hh.le) ?_
  · have htest := hcont _ (FKCRT.mapSpace_valid (edgeScale_pos P n) _)
      (hghp.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ)))
    have htree := hG (hx.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at htree
    rw [FKCRT.markedMapTest,dite_eq_left hcompat]
    have ht := abs_sub_le
      (F (FKCRT.mapSpace (edgeScale P n) ((FKCRT.rootedWordEquiv n).symm ((CoreTree.successfulMarkedEquiv n).symm y)).1))
      (F (FKCRT.treeSpace f)) (F (FKCRT.treeSpace (actualHeight P n x)))
    rw [abs_sub_comm (F (FKCRT.treeSpace f))] at ht
    linarith
  have hb₁ := mul_le_mul_of_nonneg_left hcore (edgeScale_pos P n).le
  have hb₂ := mul_le_mul_of_nonneg_left (hN n hn).1 ha.le
  have har : 8*a*L≤δ/4 := by
    have hh : a*(32*(L+1))=δ := by
      dsimp [a]
      field_simp
    nlinarith [mul_nonneg ha.le hL.le]
  have hrδ : r≤δ/16 := min_le_right _ _
  nlinarith

end FKCRT.Inventory
end

end OAI
