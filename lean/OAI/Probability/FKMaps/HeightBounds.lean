import OAI.Probability.FKMaps.ConditionedWalk

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma LadderEnumeration.prefixMaximum {S : ℕ → ℤ} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    prefixMaximum S n = S (τ (renewalCount τ n)) :=
  prefixMaximum_eq (renewalCount_spec h.zero n) (fun _ hk => h.maximum hk)

lemma prefix_record_remainder {x : ℕ → ℕ} (hx : HasAllLadders x)
    (ν ε A : ℝ) (h : ∀ r, |renewalLevel r x-ν*r| ≤ ε*renewalLevel r x+A) (n : ℕ) :
    |(prefixMaximum (integerSum x) n:ℝ)-ν*(weakRecords (integerSum x) n).card| ≤
      ε*(prefixMaximum (integerSum x) n:ℝ)+A := by
  rw [(ladderTime_enumeration hx).prefixMaximum]
  exact record_count_remainder hx ν ε A h n

lemma CriticalEvenOffspring.prefix_record_uniform_remainder (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᵐ x ∂p.streamLaw, ∃ A : ℕ, ∀ n,
      |(prefixMaximum (integerSum x) n:ℝ)-(p.variance/2)*(weakRecords (integerSum x) n).card| ≤
        ε*(prefixMaximum (integerSum x) n:ℝ)+A := by
  filter_upwards [p.ae_all_ladders,p.renewal_uniform_remainder hε] with x hx hrem
  obtain ⟨A,hA⟩ := hrem
  exact ⟨A,fun n => prefix_record_remainder hx _ _ _ hA n⟩

lemma CriticalEvenOffspring.prefix_record_remainder_probability (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun A : ℕ => p.streamLaw {x | ∃ n,
      ε*(prefixMaximum (integerSum x) n:ℝ)+A <
        |(prefixMaximum (integerSum x) n:ℝ)-(p.variance/2)*(weakRecords (integerSum x) n).card|})
      atTop (𝓝 0) := by
  have hb (A : ℕ) : p.streamLaw {x | ∃ n,
      ε*(prefixMaximum (integerSum x) n:ℝ)+A <
        |(prefixMaximum (integerSum x) n:ℝ)-(p.variance/2)*(weakRecords (integerSum x) n).card|} ≤
      p.streamLaw {x | ∃ r, ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|} := by
    apply measure_mono_ae
    filter_upwards [p.ae_all_ladders] with x hx
    rintro ⟨n,hn⟩
    refine ⟨renewalCount (ladderTime x) n, ?_⟩
    rwa [(ladderTime_enumeration hx).prefixMaximum,
      (ladderTime_enumeration hx).card_records, ladderTime_level_real hx] at hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (p.renewal_remainder_probability hε) (fun _ => bot_le) hb

lemma le_prefixMaximum (S : ℕ → ℤ) {i n : ℕ} (hi : i≤n) :
    S i ≤ prefixMaximum S n :=
  Finset.le_sup' S (Finset.mem_range.mpr (by omega))

lemma prefixMaximum_le {S : ℕ → ℤ} {n : ℕ} {a : ℤ}
    (h : ∀ k, k≤n → S k≤a) : prefixMaximum S n≤a :=
  Finset.sup'_le _ _ (fun k hk => h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk))

lemma prefixMaximum_mono (S : ℕ → ℤ) {m n : ℕ} (h : m≤n) :
    prefixMaximum S m≤prefixMaximum S n :=
  prefixMaximum_le fun _ hk => le_prefixMaximum S (hk.trans h)

lemma prefixMaximum_attained (S : ℕ → ℤ) (n : ℕ) :
    ∃ k≤n, prefixMaximum S n = S k := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n+1)) Finset.nonempty_range_add_one S
  exact ⟨k,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk,he⟩

lemma CriticalEvenOffspring.integerSum_scaled (p : CriticalEvenOffspring) (x : ℕ → ℕ) (n : ℕ) :
    (integerSum x n:ℝ)=p.sigma*(∑ j∈Finset.range n,p.streamStep j x) := by
  simp only [integerSum,Int.cast_sum,Int.cast_sub,Int.cast_natCast,Int.cast_one,
    streamStep,standardStep,← Finset.sum_div]
  field_simp [p.sigma_pos.ne']

lemma CriticalEvenOffspring.prefix_maximum_bound (p : CriticalEvenOffspring)
    {N : ℕ} (hN : 0<N) {R : ℝ} (hR : 0<R) :
    p.streamLaw.real {x | p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ)} ≤ 1/R^2 := by
  have hb := independent_sum_scaled_maximal_bound p.streamStep
    (fun _ => by unfold streamStep; fun_prop) p.streamStep_memLp
    p.streamStep_indep p.streamStep_integral (fun k => (p.streamStep_integral_sq k).le) hN hR
  apply (measureReal_mono ?_).trans hb
  intro x hx
  obtain ⟨k,hk,he⟩ := prefixMaximum_attained (integerSum x) N
  refine ⟨k,hk,?_⟩
  change p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ) at hx
  rw [he,p.integerSum_scaled] at hx
  have hh : R*Real.sqrt N ≤ ∑ j∈Finset.range k,p.streamStep j x := by
    apply (mul_le_mul_iff_right₀ p.sigma_pos).mp
    simpa only [mul_assoc] using hx
  exact hh.trans (le_abs_self _)

lemma CriticalEvenOffspring.prefix_record_error_bound (p : CriticalEvenOffspring)
    {N : ℕ} (hN : 0<N) {R ε : ℝ} (hR : 0<R) (hε : 0≤ε) (A : ℕ) :
    p.streamLaw.real {x | ∃ k≤N,
      ε*(p.sigma*R*Real.sqrt N)+A <
        |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} ≤
      (p.streamLaw {x | ∃ r, ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}).toReal + 1/R^2 := by
  let E : Set (ℕ → ℕ) := {x | ∃ r, ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}
  let F : Set (ℕ → ℕ) := {x | p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ)}
  have hs : ∀ᵐ x ∂p.streamLaw, (∃ k≤N, ε*(p.sigma*R*Real.sqrt N)+A <
      |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|) →
      x∈E∪F := by
    filter_upwards [p.ae_all_ladders] with x hx
    rintro ⟨k,hk,hbad⟩
    by_cases he : x∈E
    · exact Or.inl he
    apply Or.inr
    by_contra hf
    have hrem : ∀ r, |renewalLevel r x-(p.variance/2)*r| ≤ ε*renewalLevel r x+A := by
      simpa only [E,Set.mem_ofPred_eq,not_exists,not_lt] using he
    have hmax : (prefixMaximum (integerSum x) k:ℝ) ≤ p.sigma*R*Real.sqrt N := by
      exact (Int.cast_le.mpr (prefixMaximum_mono _ hk)).trans (le_of_lt (not_le.mp hf))
    exact (not_lt_of_ge ((prefix_record_remainder hx _ _ _ hrem k).trans
      (add_le_add (mul_le_mul_of_nonneg_left hmax hε) le_rfl))) hbad
  calc
    _ ≤ p.streamLaw.real (E∪F) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    _ ≤ p.streamLaw.real E+p.streamLaw.real F := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (p.prefix_maximum_bound hN hR)

/-- Finite variance suffices for the uniform renewal-record approximation on
an unconditioned iid prefix; no upper exponential moment is used. -/
theorem CriticalEvenOffspring.iid_prefix_record_error (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun N : ℕ => p.streamLaw.real {x | ∃ k≤N,
      δ*Real.sqrt N <
        |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro η hη
    let R := Real.sqrt (4/η)
    have hR : 0<R := Real.sqrt_pos.mpr (by positivity)
    have hR2 : R^2=4/η := Real.sq_sqrt (by positivity)
    have htail : 1/R^2=η/4 := by rw [hR2]; field_simp
    have hσ := p.sigma_pos
    let ε := δ/(2*p.sigma*R)
    have hε : 0<ε := div_pos hδ (by positivity)
    have heq : ε*(p.sigma*R)=δ/2 := by dsimp [ε]; field_simp [hR.ne',hσ.ne']
    have hlim : Tendsto (fun A : ℕ => (p.streamLaw {x | ∃ r,
        ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}).toReal)
        atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_zero,Function.comp_def] using
        (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠∞)).comp (p.renewal_remainder_probability hε)
    obtain ⟨A,hA⟩ := (hlim.eventually (eventually_lt_nhds (show (0:ℝ)<η/2 from half_pos hη))).exists
    have hscale : Tendsto (fun N : ℕ => δ/2*Real.sqrt N) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (half_pos hδ)
    filter_upwards [hscale.eventually_ge_atTop (A:ℝ),eventually_gt_atTop 0] with N hN hNpos
    have hbound := p.prefix_record_error_bound hNpos hR hε.le A
    have hs : ε*(p.sigma*R*Real.sqrt N)+A ≤ δ*Real.sqrt N := by
      rw [← mul_assoc,heq]
      linarith
    have hmono : p.streamLaw.real {x | ∃ k≤N,
        δ*Real.sqrt N <
          |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} ≤
        p.streamLaw.real {x | ∃ k≤N, ε*(p.sigma*R*Real.sqrt N)+A <
          |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro x ⟨k,hk,hx⟩
      exact ⟨k,hk,hs.trans_lt hx⟩
    apply (hmono.trans hbound).trans_lt
    rw [htail]
    linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma map_cond_preimage {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) {f : Ω → Ξ} (hf : Measurable f) {s : Set Ξ} (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond,ProbabilityTheory.cond,Measure.map_smul _ hf.aemeasurable,
    ← Measure.restrict_map hf hs,Measure.map_apply hf hs]

def streamPrefix (N : ℕ) (x : ℕ → ℕ) : Fin N → ℕ := fun i => x i.val

lemma measurable_streamPrefix (N : ℕ) : Measurable (streamPrefix N) :=
  Measurable.of_eval (fun index => measurable_pi_apply index.val)

lemma totalStep_streamPrefix (N : ℕ) (x : ℕ → ℕ) :
    totalStep (streamPrefix N x)=integerSum x N := by
  exact Fin.sum_univ_eq_sum_range (fun k => ((x k:ℤ)-1)) N

lemma CriticalEvenOffspring.streamPrefix_hasLaw (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (streamPrefix N) (p.iidLaw N) p.streamLaw := p.stream_restrict_law N

def CriticalEvenOffspring.streamBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) :
    Measure (ℕ → ℕ) := cond p.streamLaw {x | integerSum x (2*n+1)=-1}

lemma CriticalEvenOffspring.streamBridge_restrict (p : CriticalEvenOffspring) (n : ℕ) :
    HasLaw (streamPrefix (2*n+1)) (p.iidBridgeLaw n) (p.streamBridgeLaw n) := by
  refine ⟨(measurable_streamPrefix _).aemeasurable,?_⟩
  have hh := map_cond_preimage p.streamLaw (measurable_streamPrefix (2*n+1))
    (show MeasurableSet {d : Fin (2*n+1) → ℕ | totalStep d=-1} from by measurability)
  simpa only [streamBridgeLaw,iidBridgeLaw,Set.preimage_ofPred_eq,totalStep_streamPrefix,
    (p.streamPrefix_hasLaw (2*n+1)).map_eq] using hh

instance (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.streamBridgeLaw n) := by
  have : IsProbabilityMeasure ((p.streamBridgeLaw n).map (streamPrefix (2*n+1))) := by
    rw [(p.streamBridge_restrict n).map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (measurable_streamPrefix (2*n+1)).aemeasurable

def arrayStream {N : ℕ} (d : Fin N → ℕ) : ℕ → ℕ :=
  fun k => if h:k<N then d ⟨k,h⟩ else 0

lemma integerSum_arrayStream_prefix (N : ℕ) (x : ℕ → ℕ) {k : ℕ} (hk : k ≤ N) :
    integerSum (arrayStream (streamPrefix N x)) k = integerSum x k := by
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  simp only [arrayStream,streamPrefix,dite_eq_left ((Finset.mem_range.mp hi).trans_le hk)]

def recordError (ν : ℝ) (S : ℕ → ℤ) (k : ℕ) : ℝ :=
  |(prefixMaximum S k:ℝ)-ν*(weakRecords S k).card|

lemma recordError_congr {ν : ℝ} {S T : ℕ → ℤ} {k : ℕ}
    (h : ∀ j, j ≤ k → S j=T j) : recordError ν S k=recordError ν T k := by
  rw [recordError,recordError,prefixMaximum_congr h,weakRecords_congr_prefix h]

lemma recordError_arrayStream_prefix (N : ℕ) (x : ℕ → ℕ) {k : ℕ} (hk : k ≤ N) (ν : ℝ) :
    recordError ν (integerSum (arrayStream (streamPrefix N x))) k = recordError ν (integerSum x) k :=
  recordError_congr fun _ hj => integerSum_arrayStream_prefix N x (hj.trans hk)

lemma iidSplit_streamPrefix (m r : ℕ) (x : ℕ → ℕ) :
    (iidSplit m r (streamPrefix (m+r) x)).1=streamPrefix m x := rfl

lemma CriticalEvenOffspring.prefix_domination_stream (p : CriticalEvenOffspring)
    {n J : ℕ} {K : ℝ} (hdom : p.PrefixDominatedFraction (2*n+1) J K)
    {m r : ℕ} (hs : m+r=2*n+1) (hfrac : 2*n+1 ≤ J*r) (E : Set (Fin m → ℕ)) :
    (p.streamBridgeLaw n).real (streamPrefix m ⁻¹' E)  ≤ 
      K*p.streamLaw.real (streamPrefix m ⁻¹' E) := by
  have hmap := (p.streamPrefix_hasLaw m).measurePreserving (measurable_streamPrefix m)
  rw [hmap.measureReal_preimage (by measurability)]
  have hb := hdom m r hs hfrac E
  have heq : (cond (p.iidLaw (m+r)) {d | totalStep d=-1})=
      (p.streamBridgeLaw n).map (streamPrefix (m+r)) := by
    rw [hs]
    exact (p.streamBridge_restrict n).map_eq.symm
  rw [heq] at hb
  have hm : Measurable (streamPrefix (m+r)) := measurable_streamPrefix _
  rw [map_measureReal_apply hm (by measurability)] at hb
  exact hb

lemma CriticalEvenOffspring.prefix_record_domination (p : CriticalEvenOffspring)
    {n J : ℕ} {K : ℝ} (hdom : p.PrefixDominatedFraction (2*n+1) J K)
    {m r : ℕ} (hs : m+r=2*n+1) (hfrac : 2*n+1 ≤ J*r) (a : ℝ) :
    (p.streamBridgeLaw n).real {x | ∃ k ≤ m, a<recordError (p.variance/2) (integerSum x) k}  ≤ 
      K*p.streamLaw.real {x | ∃ k ≤ m, a<recordError (p.variance/2) (integerSum x) k} := by
  let E : Set (Fin m → ℕ) := {d | ∃ k ≤ m, a<recordError (p.variance/2) (integerSum (arrayStream d)) k}
  have he : streamPrefix m ⁻¹' E={x | ∃ k ≤ m, a<recordError (p.variance/2) (integerSum x) k} := by
    ext x
    change (∃ k ≤ m, a<recordError (p.variance/2) (integerSum (arrayStream (streamPrefix m x))) k) ↔ _
    constructor <;> rintro ⟨k,hk,he⟩ <;> refine ⟨k,hk,?_⟩
    · rwa [recordError_arrayStream_prefix m x hk] at he
    · rwa [recordError_arrayStream_prefix m x hk]
  simpa only [he] using p.prefix_domination_stream hdom hs hfrac E

/-- The uniform record approximation survives conditioning on every fixed
proper prefix. The remaining terminal segment is handled separately. -/
theorem CriticalEvenOffspring.bridge_prefix_record_error (p : CriticalEvenOffspring)
    {J : ℕ} (hJ : 0<J) (m r : ℕ → ℕ)
    (hs : ∀ n, m n+r n=2*n+1) (hfrac : ∀ᶠ n in atTop, 2*n+1 ≤ J*r n)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => (p.streamBridgeLaw n).real {x | ∃ k ≤ m n,
      δ*Real.sqrt ((2*n+1:ℕ):ℝ)<recordError (p.variance/2) (integerSum x) k}) atTop (𝓝 0) := by
  obtain ⟨K,hK,hdom⟩ := p.bridge_prefix_domination_fraction J hJ
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hi := (p.iid_prefix_record_error hδ).comp hN
  have hlim := hi.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [hdom,hfrac] with n hn hf
  have hb := p.prefix_record_domination hn (hs n) hf (δ*Real.sqrt ((2*n+1:ℕ):ℝ))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hK.le
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro x ⟨k,hk,hx⟩
  exact ⟨k,by dsimp; have hh := hs n; omega,hx⟩

lemma CriticalEvenOffspring.streamBridge_reverse (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseFirst (2*n+1)) (p.streamBridgeLaw n) (p.streamBridgeLaw n) := by
  apply measurePreserving_cond (reverseFirst_preserving p (2*n+1))
    (measurableSet_eq_fun (measurable_integerSum _) measurable_const)
  ext x
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,integerSum_reverseFirst x (2*n+1) (2*n+1) le_rfl,
    Nat.sub_self,integerSum_zero,sub_zero]

lemma CriticalEvenOffspring.integer_maximal_bound (p : CriticalEvenOffspring)
    (r : ℕ) {a : ℝ} (ha : 0<a) :
    p.streamLaw.real {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|}  ≤  (r:ℝ)*p.sigma^2/a^2 := by
  have hb := independent_sum_maximal_bound p.streamStep
    (fun _ => by unfold streamStep; fun_prop) p.streamStep_memLp p.streamStep_indep
    p.streamStep_integral r (div_pos ha p.sigma_pos)
  simp only [p.streamStep_integral_sq,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hb
  have hs : {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|} ⊆
      {x | ∃ k ≤ r, a/p.sigma ≤ |∑ j∈Finset.range k,p.streamStep j x|} := by
    rintro x ⟨k,hk,hx⟩
    refine ⟨k,hk,?_⟩
    rw [p.integerSum_scaled,abs_mul,abs_of_pos p.sigma_pos] at hx
    exact (div_le_iff₀ p.sigma_pos).mpr (by simpa [mul_comm] using hx)
  apply ((measureReal_mono hs).trans hb).trans_eq
  field_simp

lemma integerSum_prefix_event (r : ℕ) (a : ℝ) :
    streamPrefix r ⁻¹' {d | ∃ k ≤ r, a ≤ |(integerSum (arrayStream d) k:ℝ)|}=
      {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|} := by
  ext x
  change (∃ k ≤ r, a ≤ |(integerSum (arrayStream (streamPrefix r x)) k:ℝ)|) ↔ _
  constructor <;> rintro ⟨k,hk,he⟩ <;> refine ⟨k,hk,?_⟩
  · rwa [integerSum_arrayStream_prefix r x hk] at he
  · rwa [integerSum_arrayStream_prefix r x hk]

lemma CriticalEvenOffspring.bridge_initial_maximal_bound (p : CriticalEvenOffspring)
    {n : ℕ} {K : ℝ} (hK : 0 ≤ K) (hdom : p.PrefixDominatedFraction (2*n+1) 2 K)
    {r : ℕ} (hr : 2*r ≤ 2*n+1) {a : ℝ} (ha : 0<a) :
    (p.streamBridgeLaw n).real {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|}  ≤  K*((r:ℝ)*p.sigma^2/a^2) := by
  let E : Set (Fin r → ℕ) := {d | ∃ k ≤ r, a ≤ |(integerSum (arrayStream d) k:ℝ)|}
  have hh := p.prefix_domination_stream hdom (m := r) (r := 2*n+1-r) (by omega) (by omega) E
  rw [integerSum_prefix_event] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (p.integer_maximal_bound r ha) hK)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma weakRecords_mono (S : ℕ → ℤ) {m n : ℕ} (h : m ≤ n) :
    weakRecords S m ⊆ weakRecords S n := by
  intro k hk
  obtain ⟨hk0,hkm,hrec⟩ := (mem_weakRecords S m k).mp hk
  exact (mem_weakRecords S n k).mpr ⟨hk0,hkm.trans h,hrec⟩

/-- New absolute weak records are a subset of records in the translated suffix. -/
lemma weakRecords_suffix_card_le (S : ℕ → ℤ) {m n : ℕ} (h : m ≤ n) :
    (weakRecords S n).card  ≤  (weakRecords S m).card+
      (weakRecords (fun k => S (m+k)-S m) (n-m)).card := by
  classical
  have hs : weakRecords S n ⊆ weakRecords S m ∪
      (weakRecords (fun k => S (m+k)-S m) (n-m)).image (fun k => m+k) := by
    intro k hk
    obtain ⟨hk0,hkn,hrec⟩ := (mem_weakRecords S n k).mp hk
    by_cases hkm : k ≤ m
    · exact Finset.mem_union_left _ ((mem_weakRecords S m k).mpr ⟨hk0,hkm,hrec⟩)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨k-m,?_,by omega⟩
    apply (mem_weakRecords ..).mpr
    refine ⟨by omega,by omega,?_⟩
    intro j hj
    have hh := hrec (m+j) (by omega)
    have he : m+(k-m)=k := by omega
    rw [he]
    omega
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    (add_le_add le_rfl (Finset.card_image_le)))

lemma weakRecords_suffix_of_ladder_level (x : ℕ → ℕ) {m n h : ℕ} (hmn : m ≤ n)
    (hx : HasAllLadders (streamShift m x)) {a : ℝ}
    (hla : a  ≤  renewalLevel h (streamShift m x))
    (hosc : ∀ k, m ≤ k → k ≤ n → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a) :
    (weakRecords (integerSum x) n).card  ≤  (weakRecords (integerSum x) m).card+h := by
  have hb := weakRecords_suffix_card_le (integerSum x) hmn
  have he : (fun k => integerSum x (m+k)-integerSum x m)=integerSum (streamShift m x) := by
    funext k
    exact (integerSum_shift x m k).symm
  rw [he,(ladderTime_enumeration hx).card_records] at hb
  have hcount : renewalCount (ladderTime (streamShift m x)) (n-m) ≤ h := by
    by_contra hn
    have htime : ladderTime (streamShift m x) h ≤ n-m :=
      (le_renewalCount_iff (ladderTime_enumeration hx).strictMono
        (ladderTime_enumeration hx).zero h (n-m)).mp (by omega)
    have hosc' := hosc (m+ladderTime (streamShift m x) h) (by omega) (by omega)
    rw [← ladderTime_level_real hx] at hla
    rw [integerSum_shift] at hla
    push_cast at hla
    linarith
  omega

lemma prefixMaximum_tail_le {S : ℕ → ℤ} {m n : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hosc : ∀ k, m ≤ k → k ≤ n → (S k:ℝ)-(S m:ℝ) ≤ a) :
    (prefixMaximum S n:ℝ)  ≤  (prefixMaximum S m:ℝ)+a := by
  obtain ⟨k,hk,he⟩ := prefixMaximum_attained S n
  rw [he]
  by_cases hkm : k ≤ m
  · exact (Int.cast_le.mpr (le_prefixMaximum S hkm)).trans (le_add_of_nonneg_right ha)
  · have hh := hosc k (by omega) hk
    have hsup : (S m:ℝ) ≤ prefixMaximum S m := Int.cast_le.mpr (le_prefixMaximum S le_rfl)
    linarith

/-- Uniform numerical estimate used to pass from a truncated bridge to its
full record count. It needs only attained maxima and a one-sided suffix bound. -/
lemma prefix_record_error_tail {x : ℕ → ℕ} {m n h : ℕ} (hmn : m ≤ n)
    (hx : HasAllLadders (streamShift m x)) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a)
    (hla : a  ≤  renewalLevel h (streamShift m x))
    (hosc : ∀ k, m ≤ k → k ≤ n → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a) :
    |(prefixMaximum (integerSum x) n:ℝ)-ν*(weakRecords (integerSum x) n).card|  ≤ 
      |(prefixMaximum (integerSum x) m:ℝ)-ν*(weakRecords (integerSum x) m).card|+a+ν*h := by
  have hcount := weakRecords_suffix_of_ladder_level x hmn hx hla hosc
  have hcount' : ((weakRecords (integerSum x) n).card:ℝ)  ≤ 
      ((weakRecords (integerSum x) m).card:ℝ)+h := by exact_mod_cast hcount
  have hcountlo : ((weakRecords (integerSum x) m).card:ℝ)  ≤ 
      ((weakRecords (integerSum x) n).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (weakRecords_mono (integerSum x) hmn)
  have hmax := prefixMaximum_tail_le ha (fun k hk hn => (hosc k hk hn).le)
  have hmaxlo : (prefixMaximum (integerSum x) m:ℝ)  ≤  prefixMaximum (integerSum x) n :=
    Int.cast_le.mpr (prefixMaximum_mono _ hmn)
  apply abs_le.mpr
  have hh := abs_le.mp (le_refl |(prefixMaximum (integerSum x) m:ℝ)-ν*(weakRecords (integerSum x) m).card|)
  constructor <;> nlinarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma cond_real_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E) (B : Set Ω) :
    (cond μ E).real B ≤ μ.real B / μ.real E := by
  rw [measureReal_def,cond_apply hE,ENNReal.toReal_mul,ENNReal.toReal_inv]
  change (μ.real E)⁻¹ * μ.real (E ∩ B) ≤ _
  rw [div_eq_mul_inv,mul_comm (μ.real B)]
  exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right) (inv_nonneg.mpr measureReal_nonneg)

lemma CriticalEvenOffspring.stream_endpoint_probability (p : CriticalEvenOffspring) (N : ℕ) :
    p.streamLaw.real {x | integerSum x N = -1} =
      (p.iidLaw N).real {d | totalStep d = -1} := by
  have hh := (p.streamPrefix_hasLaw N).measurePreserving (measurable_streamPrefix N)
  simpa only [Set.preimage_ofPred_eq,totalStep_streamPrefix] using
    hh.measureReal_preimage (show MeasurableSet {d : Fin N → ℕ | totalStep d = -1} from by measurability).nullMeasurableSet

lemma CriticalEvenOffspring.stream_endpoint_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n => Real.sqrt ((2*n+1:ℕ):ℝ)*
      p.streamLaw.real {x | integerSum x (2*n+1) = -1}) atTop (𝓝 p.bridgeConstant) := by
  simpa only [p.stream_endpoint_probability] using p.iid_endpoint_limit

lemma CriticalEvenOffspring.streamBridge_shift_ladders (p : CriticalEvenOffspring) (n m : ℕ) :
    ∀ᵐ x ∂p.streamBridgeLaw n, HasAllLadders (streamShift m x) :=
  cond_absolutelyContinuous.ae_le ((p.streamShift_preserving m).quasiMeasurePreserving.ae p.ae_all_ladders)

lemma CriticalEvenOffspring.bridge_shift_ladder_bound (p : CriticalEvenOffspring)
    {c ρ : ℝ} (hρ : 0 ≤ ρ)
    (hb : ∀ h, p.streamLaw {x | renewalLevel h x ≤ c*h} ≤ ENNReal.ofReal (ρ^h))
    (n m h : ℕ) :
    (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift m x) ≤ c*h} ≤
      ρ^h / p.streamLaw.real {x | integerSum x (2*n+1) = -1} := by
  have hr : MeasurableSet {x | renewalLevel h x ≤ c*h} :=
    measurableSet_le (measurable_renewalLevel h) measurable_const
  have ht := (p.streamShift_preserving m).measureReal_preimage hr.nullMeasurableSet
  have hreal : p.streamLaw.real {x | renewalLevel h x ≤ c*h} ≤ ρ^h := by
    exact (ENNReal.toReal_mono (by finiteness) (hb h)).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hρ _))
  apply (cond_real_le p.streamLaw (measurableSet_eq_fun (measurable_integerSum _) measurable_const) _).trans
  exact div_le_div_of_nonneg_right (ht.le.trans hreal) measureReal_nonneg

lemma CriticalEvenOffspring.bridge_terminal_maximal_bound (p : CriticalEvenOffspring)
    {n : ℕ} {K : ℝ} (hK : 0 ≤ K) (hdom : p.PrefixDominatedFraction (2*n+1) 2 K)
    {r : ℕ} (hr : 2*r ≤ 2*n+1) {a : ℝ} (ha : 0<a) :
    (p.streamBridgeLaw n).real {x | ∃ k, 2*n+1-r ≤ k ∧ k ≤ 2*n+1 ∧
      a ≤ (integerSum x k:ℝ)-(integerSum x (2*n+1-r):ℝ)} ≤ K*((r:ℝ)*p.sigma^2/(a/2)^2) := by
  let E : Set (ℕ → ℕ) := {x | ∃ k ≤ r, a/2 ≤ |(integerSum x k:ℝ)|}
  have hsub : {x | ∃ k, 2*n+1-r ≤ k ∧ k ≤ 2*n+1 ∧
      a ≤ (integerSum x k:ℝ)-(integerSum x (2*n+1-r):ℝ)} ⊆
      reverseFirst (2*n+1) ⁻¹' E := by
    rintro x ⟨k,hkm,hkn,hx⟩
    by_contra hn
    have hn' : ∀ j ≤ r, |(integerSum (reverseFirst (2*n+1) x) j:ℝ)| < a/2 := by
      simpa only [Set.mem_preimage,E,Set.mem_ofPred_eq,not_exists,not_and,not_le] using hn
    have h1 := hn' r le_rfl
    have h2 := hn' (2*n+1-k) (by omega)
    rw [integerSum_reverseFirst x (2*n+1) r (by omega)] at h1
    rw [integerSum_reverseFirst x (2*n+1) (2*n+1-k) (by omega),Nat.sub_sub_self hkn] at h2
    push_cast at h1 h2
    have h1' := (abs_lt.mp h1).2
    have h2' := (abs_lt.mp h2).1
    linarith
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => (MeasurableSet.const (k ≤ r)).inter
      (measurableSet_le measurable_const ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_integerSum k)).abs)
  have hh := (p.streamBridge_reverse n).measureReal_preimage hE.nullMeasurableSet
  exact (measureReal_mono hsub).trans (hh.le.trans (p.bridge_initial_maximal_bound hK hdom hr (half_pos ha)))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma tendsto_natCeil_comp_atTop {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun n => ⌈s n⌉₊) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hs.eventually (eventually_ge_atTop (b:ℝ))] with n hn
  exact_mod_cast hn.trans (Nat.le_ceil (s n))

lemma polynomial_geometric_ceil {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) (k : ℕ) :
    Tendsto (fun n => (s n)^k*ρ^⌈ε*s n⌉₊) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ⌈ε*s n⌉₊) atTop atTop :=
    tendsto_natCeil_comp_atTop (hs.const_mul_atTop hε)
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one k hρ hρ1).comp hh).div_const (ε^k)
  simp only [zero_div] at ht
  apply squeeze_zero (fun n => mul_nonneg (pow_nonneg (hs0 n) _) (pow_nonneg hρ _)) ?_ ht
  intro n
  have hr : s n ≤ (⌈ε*s n⌉₊:ℝ)/ε := (le_div_iff₀ hε).mpr (by simpa [mul_comm] using Nat.le_ceil (ε*s n))
  calc
    (s n)^k*ρ^⌈ε*s n⌉₊ ≤ ((⌈ε*s n⌉₊:ℝ)/ε)^k*ρ^⌈ε*s n⌉₊ := by gcongr; exact hs0 n
    _ = _ := by dsimp; rw [div_pow]; ring

lemma odd_size_tendsto : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id

lemma odd_sqrt_tendsto : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1:ℕ):ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp odd_size_tendsto)

lemma CriticalEvenOffspring.bridge_geometric_vanish (p : CriticalEvenOffspring)
    {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) :
    Tendsto (fun n => ρ^⌈ε*Real.sqrt ((2*n+1:ℕ):ℝ)⌉₊ /
      p.streamLaw.real {x | integerSum x (2*n+1) = -1}) atTop (𝓝 0) := by
  have ht := (polynomial_geometric_ceil odd_sqrt_tendsto (fun _ => Real.sqrt_nonneg _) hε hρ hρ1 1).div
    p.stream_endpoint_limit p.bridgeConstant_pos.ne'
  simp only [zero_div,pow_one] at ht
  convert ht using 1
  funext n
  exact (mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne').symm

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.bridge_record_tail_bound (p : CriticalEvenOffspring)
    {n m r h : ℕ} (hs : m+r=2*n+1) {t a : ℝ} (ha : 0 ≤ a) :
    (p.streamBridgeLaw n).real {x | t+a+(p.variance/2)*h<recordError (p.variance/2) (integerSum x) (2*n+1)} ≤
      (p.streamBridgeLaw n).real {x | t<recordError (p.variance/2) (integerSum x) m} +
      (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift m x) ≤ a} +
      (p.streamBridgeLaw n).real {x | ∃ k, m ≤ k ∧ k ≤ 2*n+1 ∧
          a ≤ (integerSum x k:ℝ)-(integerSum x m:ℝ)} := by
  let A : Set (ℕ → ℕ) := {x | t<recordError (p.variance/2) (integerSum x) m}
  let B : Set (ℕ → ℕ) := {x | renewalLevel h (streamShift m x) ≤ a}
  let C : Set (ℕ → ℕ) := {x | ∃ k, m ≤ k ∧ k ≤ 2*n+1 ∧ a ≤ (integerSum x k:ℝ)-(integerSum x m:ℝ)}
  have hsub : ∀ᵐ x ∂p.streamBridgeLaw n, t+a+(p.variance/2)*h<recordError (p.variance/2) (integerSum x) (2*n+1) →
      x ∈ (A ∪ B) ∪ C := by
    filter_upwards [p.streamBridge_shift_ladders n m] with x hx
    intro hb
    by_contra hn
    have hn' : ¬x∈A ∧ ¬x∈B ∧ ¬x∈C := by simpa only [Set.mem_union,not_or,and_assoc] using hn
    have hA : recordError (p.variance/2) (integerSum x) m ≤ t := le_of_not_gt hn'.1
    have hB : a < renewalLevel h (streamShift m x) := lt_of_not_ge hn'.2.1
    have hC : ∀ k, m ≤ k → k ≤ 2*n+1 → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a := by
      simpa only [C,Set.mem_ofPred_eq,not_exists,not_and,not_le] using hn'.2.2
    have hh := prefix_record_error_tail (x := x) (h := h) (by omega : m ≤ 2*n+1)
      hx (half_pos p.variance_pos).le ha hB.le hC
    change recordError _ _ _ ≤ recordError _ _ _+a+(p.variance/2)*h at hh
    exact (not_lt_of_ge (hh.trans (by linarith))) hb
  have hb := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hb.trans ((measureReal_union_le (A ∪ B) C).trans
    (add_le_add (measureReal_union_le A B) le_rfl))

lemma terminal_ratio_bound {N r J : ℕ} (hN : 0<N) (hJ : 0<J) (hr : J*r ≤ N)
    {c ε K σ : ℝ} (hc : 0<c) (hε : 0<ε) (hK : 0 ≤ K) :
    K*((r:ℝ)*σ^2/(c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2)^2) ≤
      4*K*σ^2/(c^2*ε^2*(J:ℝ)) := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hJ' : (0:ℝ)<J := by exact_mod_cast hJ
  have hceil := Nat.le_ceil (ε*Real.sqrt (N:ℝ))
  have hden : 0<c*ε*Real.sqrt (N:ℝ)/2 := by positivity
  have hdiv : (r:ℝ)/(N:ℝ) ≤ 1/(J:ℝ) := by
    rw [div_le_div_iff₀ hN' hJ']
    simpa [mul_comm] using (show (J:ℝ)*r ≤ N by exact_mod_cast hr)
  calc
    K*((r:ℝ)*σ^2/(c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2)^2) ≤
        K*((r:ℝ)*σ^2/(c*ε*Real.sqrt (N:ℝ)/2)^2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
      have hbase : c*ε*Real.sqrt (N:ℝ)/2 ≤ c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2 := by
        nlinarith [mul_le_mul_of_nonneg_left hceil hc.le]
      exact pow_le_pow_left₀ hden.le hbase 2
    _ = (4*K*σ^2/(c^2*ε^2))*((r:ℝ)/(N:ℝ)) := by
      rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hN'.le]
      ring
    _ ≤ (4*K*σ^2/(c^2*ε^2))*(1/(J:ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = _ := by ring

lemma division_prefix_properties {N J : ℕ} (hJ : 2 ≤ J) (hN : J ≤ N) :
    (N-N/J)+N/J=N ∧ 2*(N/J) ≤ N ∧ N ≤ (2*J)*(N/J) := by
  have hJ0 : 0<J := by omega
  have hr : 1 ≤ N/J := (Nat.le_div_iff_mul_le hJ0).mpr (by omega)
  have hm := Nat.div_mul_le_self N J
  have hmod := Nat.mod_lt N hJ0
  have hdecomp := Nat.mod_add_div N J
  have h2 := Nat.mul_le_mul_right (N/J) hJ
  have hjr := Nat.mul_le_mul_left J hr
  have hmul : (2*J)*(N/J)=2*(J*(N/J)) := by ring
  rw [mul_comm (N/J) J] at hm
  constructor
  · exact Nat.sub_add_cancel (Nat.div_le_self N J)
  constructor
  · exact h2.trans hm
  · rw [hmul]
    omega

/-- The weak-record approximation for the **whole** conditioned bridge.
The terminal part is controlled by reversal and a second-moment maximal
inequality, not by independence at the random Vervaat cut. -/
theorem CriticalEvenOffspring.bridge_record_error (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => (p.streamBridgeLaw n).real {x |
      δ*Real.sqrt ((2*n+1:ℕ):ℝ)<recordError (p.variance/2) (integerSum x) (2*n+1)})
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hdom⟩ := p.bridge_prefix_domination_fraction 2 (by norm_num)
  obtain ⟨c,ρ,hc,hρ,hρ1,hbound⟩ := p.renewal_lower_tail
  let ν := p.variance/2
  have hν : 0<ν := half_pos p.variance_pos
  let ε := δ/(4*(c+ν))
  have hε : 0<ε := div_pos hδ (by positivity)
  have heq : (c+ν)*ε=δ/4 := by dsimp [ε]; field_simp
  let C := 4*K*p.sigma^2/(c^2*ε^2)
  have hC : 0 ≤ C := by positivity
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  have hjlim : Tendsto (fun J : ℕ => C/(J:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨J,hJ,hCJ⟩ := ((eventually_ge_atTop 2).and
    (hjlim.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity)))).exists
  have hJ0 : 0<J := by omega
  let r : ℕ → ℕ := fun n => (2*n+1)/J
  let m : ℕ → ℕ := fun n => 2*n+1-r n
  have hs : ∀ n, m n+r n=2*n+1 := fun n => Nat.sub_add_cancel (Nat.div_le_self (2*n+1) J)
  have hfrac : ∀ᶠ n in atTop, 2*n+1 ≤ (2*J)*r n := by
    filter_upwards [odd_size_tendsto.eventually_ge_atTop J] with n hn
    exact (division_prefix_properties hJ hn).2.2
  have hpre := p.bridge_prefix_record_error (by omega : 0<2*J) m r hs hfrac (half_pos hδ)
  have hgeo := p.bridge_geometric_vanish hε hρ.le hρ1
  have hlarge : ∀ᶠ n in atTop, c+ν ≤ δ/4*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (by positivity : 0<δ/4)).eventually_ge_atTop (c+ν)
  filter_upwards [hdom,odd_size_tendsto.eventually_ge_atTop J,hlarge,
    hpre.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity)),
    hgeo.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity))] with n hn hJn hln hpn hgn
  let s := Real.sqrt ((2*n+1:ℕ):ℝ)
  let h := ⌈ε*s⌉₊
  have hsp : 0<s := Real.sqrt_pos.mpr (by positivity)
  have hhp : (0:ℝ)<h := (mul_pos hε hsp).trans_le (Nat.le_ceil _)
  have hsmall : (c+ν)*h ≤ δ/2*s := by
    have hh : (h:ℝ) ≤ ε*s+1 := (Nat.ceil_lt_add_one (mul_nonneg hε.le hsp.le)).le
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ c+ν by positivity)
    have heq' := congrArg (fun t : ℝ => t*s) heq
    dsimp [s] at heq' ⊢
    nlinarith
  have hthresh : δ/2*s+c*h+ν*h ≤ δ*s := by nlinarith
  have hmono : (p.streamBridgeLaw n).real {x | δ*s<recordError ν (integerSum x) (2*n+1)} ≤
      (p.streamBridgeLaw n).real {x | δ/2*s+c*h+ν*h<recordError ν (integerSum x) (2*n+1)} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact hthresh.trans_lt hx
  have hb := p.bridge_record_tail_bound (hs n) (h := h) (t := δ/2*s) (mul_nonneg hc.le hhp.le)
  have hp : (p.streamBridgeLaw n).real {x | δ/2*s<recordError ν (integerSum x) (m n)} < η/3 := by
    apply lt_of_le_of_lt _ hpn
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact ⟨m n,le_rfl,hx⟩
  have hg : (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift (m n) x) ≤ c*h} < η/3 :=
    (p.bridge_shift_ladder_bound hρ.le hbound n (m n) h).trans_lt hgn
  have ht : (p.streamBridgeLaw n).real {x | ∃ k, m n ≤ k ∧ k ≤ 2*n+1 ∧
      c*h ≤ (integerSum x k:ℝ)-(integerSum x (m n):ℝ)} ≤ C/(J:ℝ) := by
    have hhalf : 2*r n ≤ 2*n+1 := (division_prefix_properties hJ hJn).2.1
    have hh := p.bridge_terminal_maximal_bound hK.le hn hhalf (mul_pos hc hhp)
    apply hh.trans
    have he := terminal_ratio_bound (by omega : 0<2*n+1) hJ0
      (show J*r n ≤ 2*n+1 by simpa only [r,mul_comm] using Nat.div_mul_le_self (2*n+1) J)
      hc hε hK.le (σ := p.sigma)
    exact he.trans_eq (by dsimp only [C]; ring)
  have hh := (hmono.trans hb).trans (add_le_add (add_le_add hp.le hg.le) ht)
  change (p.streamBridgeLaw n).real {x | δ*s<recordError ν (integerSum x) (2*n+1)} < η
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

instance (N : ℕ) : MeasurableSpace (Code N) := ⊤
instance (N : ℕ) : MeasurableSingletonClass (Code N) := ⟨fun _ => trivial⟩

def CriticalEvenOffspring.codeLaw (p : CriticalEvenOffspring) (n : ℕ) : Measure (Code (2*n+1)) :=
  (p.iidBridgeLaw n).map (arrayTree n)

instance (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.codeLaw n) :=
  inferInstanceAs (IsProbabilityMeasure ((p.iidBridgeLaw n).map (arrayTree n)))

lemma CriticalEvenOffspring.code_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    (∫ d,F d ∂p.codeLaw n)=∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F d := by
  rw [codeLaw,integral_map (measurable_of_countable (arrayTree n)).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  exact p.arrayTree_expectation n F

lemma integerSum_arrayStream_bridge {N : ℕ} (d : Bridge N) {k : ℕ} (hk : k ≤ N) :
    integerSum (arrayStream (bridgeEmbedding N d)) k=walk d.val k := by
  unfold integerSum walk
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val,by
    have hh := Finset.mem_filter.mp hi
    exact hh.2⟩ : Fin k))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin k => z.val) he)
  · intro i _
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,by simp [i.isLt],rfl⟩
  · intro i hi
    have hi' : i.val<k := (Finset.mem_filter.mp hi).2
    simp only [arrayStream,dite_eq_left (hi'.trans_le hk),bridgeEmbedding]
    rfl

lemma measurable_recordError_integerSum (ν : ℝ) (N : ℕ) :
    Measurable (fun x => recordError ν (integerSum x) N) := by
  have hh := (measurable_of_countable (fun d : Fin N → ℕ => recordError ν (integerSum (arrayStream d)) N)).comp
    (measurable_streamPrefix N)
  simpa only [Function.comp_def,recordError_arrayStream_prefix N _ le_rfl] using hh

def badHeightFraction {N : ℕ} (ν a : ℝ) (d : Code N) : ℝ :=
  (∑ v : Fin N, if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then (1:ℝ) else 0)/(N:ℝ)

lemma badHeightFraction_nonneg {N : ℕ} (ν a : ℝ) (d : Code N) : 0 ≤ badHeightFraction ν a d := by
  unfold badHeightFraction
  positivity

lemma recordError_reverse_array_bridge {N : ℕ} (ν : ℝ) (b : Bridge N) :
    recordError ν (reversedPath (integerSum (arrayStream (bridgeEmbedding N b))) N) N =
      recordError ν (reversedPath (walk b.val) N) N := by
  apply recordError_congr
  intro k hk
  simp only [reversedPath,integerSum_arrayStream_bridge b le_rfl,
    integerSum_arrayStream_bridge b (Nat.sub_le N k)]

lemma recordError_reverse_streamPrefix (ν : ℝ) (N : ℕ) (x : ℕ → ℕ) :
    recordError ν (reversedPath (integerSum (arrayStream (streamPrefix N x))) N) N =
      recordError ν (integerSum (reverseFirst N x)) N := by
  apply recordError_congr
  intro k hk
  rw [reversedPath,integerSum_arrayStream_prefix N x le_rfl,
    integerSum_arrayStream_prefix N x (Nat.sub_le N k),integerSum_reverseFirst x N k hk]

lemma CriticalEvenOffspring.code_average_height_error (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ) :
    (∫ d,badHeightFraction ν a d ∂p.codeLaw n) =
      (p.streamBridgeLaw n).real {x | a<recordError ν (integerSum x) (2*n+1)} := by
  classical
  let N := 2*n+1
  let F : (Fin N → ℕ) → ℝ := fun d =>
    if a<recordError ν (reversedPath (integerSum (arrayStream d)) N) N then 1 else 0
  have hsum : (∫ d,badHeightFraction ν a d ∂p.codeLaw n) = ∫ d,F d ∂p.iidBridgeLaw n := by
    rw [p.code_integral, CriticalEvenOffspring.iidBridgeLaw, p.bridge_integral_eq]
    have hh := uniform_vertex_height_error p n ν a
    unfold badHeightFraction
    convert hh using 1
    · simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    · apply Finset.sum_congr rfl
      intro b _
      dsimp only [F,N]
      rw [recordError_reverse_array_bridge]
      rfl
  rw [hsum]
  have hr := (p.streamBridge_restrict n).integral_comp (measurable_of_countable F).aestronglyMeasurable
  rw [← hr]
  have hF : (fun x => F (streamPrefix N x)) = fun x =>
      if a<recordError ν (integerSum (reverseFirst N x)) N then (1:ℝ) else 0 := by
    funext x
    simp only [F,recordError_reverse_streamPrefix]
  change (∫ x,F (streamPrefix N x) ∂p.streamBridgeLaw n)=_
  rw [hF]
  have hE : MeasurableSet {x | a<recordError ν (integerSum x) N} :=
    measurableSet_lt measurable_const (measurable_recordError_integerSum ν N)
  have hm := (p.streamBridge_reverse n).measureReal_preimage hE.nullMeasurableSet
  rw [← hm]
  exact integral_indicator_one (hE.preimage (reverseFirst_preserving p N).measurable)

/-- The expected proportion of vertices with macroscopic height/walk error
vanishes. This is an exact consequence of cyclic averaging and the full
conditioned-bridge weak-record theorem. -/
theorem CriticalEvenOffspring.average_height_error_limit (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => ∫ d,badHeightFraction (p.variance/2)
      (δ*Real.sqrt ((2*n+1:ℕ):ℝ)) d ∂p.codeLaw n) atTop (𝓝 0) := by
  simpa only [p.code_average_height_error] using p.bridge_record_error hδ

end FKCRT.TreeCoding
end

end OAI
