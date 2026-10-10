import OAI.Combinatorics.HalvingLines.Tokens

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.EdgeTrace.match_eq (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (t : S.EdgeTrace e) :
    S.match t.number t.batch ⟨e.1,t.loss⟩ = ⟨e.2,t.gain⟩ := by
  apply Subtype.ext
  have hn : (S.tokenState t.number t.batch.castSucc t.token : Fin n) ∉ S.marks t.batch.succ := by
    rw [t.source]
    exact (Finset.mem_sdiff.mp t.loss).2
  have ht := t.target
  rw [S.tokenState_succ] at ht
  change (transport _ _ (S.match t.number t.batch) _ : Fin n) = e.2 at ht
  rw [transport_of_not_mem (S.match t.number t.batch) _ hn] at ht
  convert ht using 1
  apply congrArg (fun v : ↥(S.loss t.batch) => (S.match t.number t.batch v : Fin n))
  exact Subtype.ext t.source.symm

lemma System.EdgeTrace.same_path (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (t t' : S.EdgeTrace e) :
    t.number = t'.number ∧ t.token = t'.token := by
  have hm₀ := t.match_eq S
  have hm₁ := t'.match_eq S
  rcases t with ⟨b,j,v,hs,ht,hl,hg⟩
  rcases t' with ⟨b',j',v',hs',ht',hl',hg'⟩
  have hb : b = b' := S.batch_unique ⟨hl,hg⟩ ⟨hl',hg'⟩
  subst b'
  have hj : j = j' := (matching_unique (S.lossIndex b) (S.gainIndex b)
    ⟨e.1,hl⟩ ⟨e.2,hg⟩).unique hm₀ hm₁
  refine ⟨hj,?_⟩
  apply (S.tokenState j b.castSucc).injective
  apply Subtype.ext
  rw [hs,hj,hs']

lemma System.convexOwner_of_trace (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (t : S.EdgeTrace e) :
    S.convexOwner e = (t.number,t.token.val) := by
  have he : e ∈ S.edges := (S.mem_edges e).mpr ⟨t.batch,t.loss,t.gain⟩
  rw [S.convexOwner_eq he]
  obtain ⟨hj,ht⟩ := (S.trace he).same_path S t
  rw [hj,ht]

lemma System.tokenPath_bounds (S : @System n R k a P) [NeZero a]
    (j : Fin a) (v : ↥(S.marks 0)) (b : Fin R)
    (hb : (S.tokenPath j v).point b.castSucc ≠ (S.tokenPath j v).point b.succ) :
    S.slope 0 < PlanarHalving.slope ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ) ∧
    PlanarHalving.slope ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ) < S.slope (Fin.last R) := by
  have hstep := (S.token_step j v b).resolve_left (fun h => hb (congrArg P h))
  have h := S.edge_slope b hstep.1 hstep.2
  exact ⟨(S.increasing.monotone (Fin.zero_le _)).trans_lt h.1,
    h.2.trans_le (S.increasing.monotone (Fin.le_last _))⟩

lemma System.tokenPath_segment_owner (S : @System n R k a P) [NeZero n] [NeZero a]
    (j : Fin a) (v : ↥(S.marks 0)) (b : Fin R)
    (hb : (S.tokenPath j v).point b.castSucc ≠ (S.tokenPath j v).point b.succ)
    {z : Point} (hz : z ∈ segment ℝ ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ)) :
    ∃ e ∈ S.edges, S.convexOwner e = (j,v.val) ∧ z ∈ segment ℝ (P e.1) (P e.2) := by
  have hstep := (S.token_step j v b).resolve_left (fun h => hb (congrArg P h))
  let e : Fin n × Fin n := ((S.tokenState j b.castSucc v).val,(S.tokenState j b.succ v).val)
  let t : S.EdgeTrace e := ⟨b,j,v,rfl,rfl,hstep.1,hstep.2⟩
  exact ⟨e,(S.mem_edges e).mpr ⟨b,hstep⟩,S.convexOwner_of_trace t,hz⟩

lemma System.exists_graph (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) (i : Fin a × Fin n) :
    ∃ (l u : ℝ) (g : ℝ → ℝ), S.slope 0 < l ∧ l ≤ u ∧ u < S.slope (Fin.last R) ∧
      Continuous g ∧ ConvexOn ℝ univ g ∧
      (∀ x y, x ≤ y → l*(y-x) ≤ g y-g x ∧ g y-g x ≤ u*(y-x)) ∧
      (∀ e ∈ S.edges, S.convexOwner e = i → ∀ z ∈ segment ℝ (P e.1) (P e.2), g z.1 = z.2) ∧
      (∀ z ∈ F, g z.1 = z.2 → ∃ e ∈ S.edges, S.convexOwner e = i ∧ z ∈ segment ℝ (P e.1) (P e.2)) := by
  classical
  have hspan : S.slope 0 < S.slope (Fin.last R) := S.increasing (by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hR)
  by_cases hi : i.2 ∈ S.marks 0
  · let v : ↥(S.marks 0) := ⟨i.2,hi⟩
    let C := S.tokenPath i.1 v
    have h₀ : C.point 0 ∉ F := hF _
    have h₁ : C.point (Fin.last R) ∉ F := hF _
    obtain ⟨l,u,hl,hlu,hu,hs,hclean⟩ := C.exists_clean_extension F hspan h₀ h₁ (S.tokenPath_bounds i.1 v)
    refine ⟨l,u,C.extension l u,hl,hlu,hu,
      continuous_envelope _ _,convexOn_envelope _ _,?_,?_,?_⟩
    · intro x y hxy
      exact envelope_slopes _ _ (C.extension_slopes hlu hs) hxy
    · intro e he heowner z hz
      have howner := S.convexOwner_eq he
      rw [heowner] at howner
      have hj : (S.trace he).number = i.1 := congrArg Prod.fst howner.symm
      have hv : (S.trace he).token = v := Subtype.ext (congrArg Prod.snd howner.symm)
      have hsrc : C.point (S.trace he).batch.castSucc = P e.1 := by
        simpa only [C,System.tokenPath,hj,hv] using congrArg P (S.trace he).source
      have htgt : C.point (S.trace he).batch.succ = P e.2 := by
        simpa only [C,System.tokenPath,hj,hv] using congrArg P (S.trace he).target
      have hne : C.point (S.trace he).batch.castSucc ≠ C.point (S.trace he).batch.succ := by
        rw [hsrc,htgt]
        exact fun heq => (S.drawing.right e he).ne (congrArg Prod.fst heq)
      exact C.extension_edge hs _ hne (by rwa [hsrc,htgt])
    · intro z hz hg
      obtain ⟨b,hb,hz'⟩ := hclean z hz hg
      exact S.tokenPath_segment_owner i.1 v b hb hz'
  · obtain ⟨l,hl,hu⟩ := exists_between hspan
    obtain ⟨c,hc⟩ := exists_affine_avoiding F l
    refine ⟨l,l,fun x => l*x+c,hl,le_rfl,hu,by fun_prop,?_,?_,?_,?_⟩
    · refine ⟨convex_univ, ?_⟩
      intro x _ y _ p q _ _ hpq
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => c*t) hpq]
    · intro x y _
      constructor <;> ring_nf <;> exact le_rfl
    · intro e he howner
      have ho := S.convexOwner_eq he
      rw [howner] at ho
      have hv := congrArg Prod.snd ho
      exact (hi (hv ▸ (S.trace he).token.property)).elim
    · intro z hz hg
      exact (hc z hz hg).elim

end PlanarHalving.Batches

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

structure System.FullGraphs (S : @System n R k a P) [NeZero n] [NeZero a] (F : Finset Point) where
  lower : ℝ
  upper : ℝ
  lower_lt : S.slope 0 < lower
  lower_le_upper : lower ≤ upper
  upper_lt : upper < S.slope (Fin.last R)
  graph : Fin (a*n) → ℝ → ℝ
  continuous : ∀ i, Continuous (graph i)
  convex : ∀ i, ConvexOn ℝ univ (graph i)
  slopes : ∀ i x y, x ≤ y → lower*(y-x) ≤ graph i y-graph i x ∧
    graph i y-graph i x ≤ upper*(y-x)
  edge : ∀ e ∈ S.edges, ∀ z ∈ segment ℝ (P e.1) (P e.2),
    graph (finProdFinEquiv (S.convexOwner e)) z.1 = z.2
  clean : ∀ i z, z ∈ F → graph i z.1 = z.2 → ∃ e ∈ S.edges,
    finProdFinEquiv (S.convexOwner e) = i ∧ z ∈ segment ℝ (P e.1) (P e.2)

lemma System.fullGraphs_nonempty (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) :
    Nonempty (S.FullGraphs F) := by
  classical
  choose l u g hl hlu hu hc hv hs he hclean using S.exists_graph hR F hF
  let ι := Fin a × Fin n
  let ls : Finset ℝ := Finset.univ.image l
  let us : Finset ℝ := Finset.univ.image u
  have hls : ls.Nonempty := ⟨l (0,0),Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,rfl⟩⟩
  have hus : us.Nonempty := ⟨u (0,0),Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,rfl⟩⟩
  let L := ls.min' hls
  let U := us.max' hus
  have hL i : L ≤ l i := Finset.min'_le ls _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hU i : u i ≤ U := Finset.le_max' us _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hL' : S.slope 0 < L := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem ls hls)
    change S.slope 0 < ls.min' hls
    rw [← hi]
    exact hl i
  have hU' : U < S.slope (Fin.last R) := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem us hus)
    change us.max' hus < S.slope (Fin.last R)
    rw [← hi]
    exact hu i
  refine ⟨⟨L,U,hL',(hL (0,0)).trans ((hlu (0,0)).trans (hU (0,0))),hU',
    fun i => g (finProdFinEquiv.symm i),fun i => hc _,fun i => hv _,?_,?_,?_⟩⟩
  · intro i x y hxy
    exact ⟨(mul_le_mul_of_nonneg_right (hL _) (sub_nonneg.mpr hxy)).trans (hs _ x y hxy).1,
      (hs _ x y hxy).2.trans (mul_le_mul_of_nonneg_right (hU _) (sub_nonneg.mpr hxy))⟩
  · intro e hh z hz
    simpa only [Equiv.symm_apply_apply] using he (S.convexOwner e) e hh rfl z hz
  · intro i z hz hgz
    obtain ⟨e,hh,ho,hz'⟩ := hclean _ z hz hgz
    exact ⟨e,hh,by rw [ho,Equiv.apply_symm_apply],hz'⟩

noncomputable def System.fullGraphs (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) : S.FullGraphs F :=
  Classical.choice (S.fullGraphs_nonempty hR F hF)

lemma System.FullGraphs.unique_incidence (S : @System n R k a P) [NeZero n] [NeZero a]
    {F : Finset Point} (G : S.FullGraphs F)
    (hF : ∀ z ∈ F, ∀ e ∈ S.edges, ∀ f ∈ S.edges,
      z ∈ segment ℝ (P e.1) (P e.2) → z ∈ segment ℝ (P f.1) (P f.2) → e = f)
    {z : Point} (hz : z ∈ F) {i j : Fin (a*n)}
    (hi : G.graph i z.1 = z.2) (hj : G.graph j z.1 = z.2) : i = j := by
  obtain ⟨e,he,hei,hze⟩ := G.clean i z hz hi
  obtain ⟨f,hf,hfj,hzf⟩ := G.clean j z hz hj
  have h := hF z hz e he f hf hze hzf
  rw [← hei,← hfj,h]

end PlanarHalving.Batches

namespace PlanarHalving.RankCoordinates
open Filter Set
open scoped Topology
lemma sigmoid_scale_limit {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun t : ℝ => Real.sigmoid (x*t)) atTop (𝓝 (if 0 < x then 1 else 0)) := by
  split_ifs with h
  · exact Real.tendsto_sigmoid_atTop.comp ((tendsto_const_mul_atTop_of_pos h).mpr tendsto_id)
  · exact Real.tendsto_sigmoid_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (lt_of_le_of_ne (le_of_not_gt h) hx)).mpr tendsto_id)

lemma smoothed_scale_limit {m : ℕ} (g : Fin m → ℝ → ℝ) {p : Point} (j : Fin m)
    (hj : g j p.1 = p.2) (hunique : ∀ i, g i p.1 = p.2 → i = j) :
    Tendsto (fun t : ℝ => smoothed g (1/t) p) atTop
      (𝓝 (((slot g p : ℝ) + 1/2)/m)) := by
  classical
  have hlim (i : Fin m) : Tendsto (fun t : ℝ => Real.sigmoid ((p.2-g i p.1)*t)) atTop
      (𝓝 ((if g i p.1 < p.2 then (1:ℝ) else 0) + if i = j then 1/2 else 0)) := by
    by_cases hi : i = j
    · subst i
      simp only [hj,lt_self_iff_false,ite_false,ite_true,sub_self,zero_mul,Real.sigmoid_zero,zero_add]
      simpa only [one_div] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)⁻¹) atTop (𝓝 (2:ℝ)⁻¹))
    · have hn : p.2-g i p.1 ≠ 0 := fun h => hi (hunique i (sub_eq_zero.mp h).symm)
      simpa only [sub_pos,hi,ite_false,add_zero] using sigmoid_scale_limit hn
  have ht := (tendsto_finsetSum Finset.univ (fun i _ => hlim i)).div_const (m : ℝ)
  have hs : (∑ i : Fin m, ((if g i p.1 < p.2 then (1:ℝ) else 0) + if i = j then 1/2 else 0)) =
      (slot g p : ℝ) + 1/2 := by
    rw [Finset.sum_add_distrib]
    simp [slot]
  rw [hs] at ht
  simpa only [smoothed,one_div,div_inv_eq_mul] using ht

theorem exists_smoothing_slot_error {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (F : Finset Point) (hF : ∀ p ∈ F, ∃! j, g j p.1 = p.2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ F, |smoothed g ε p - (slot g p : ℝ)/m| ≤ 2/m := by
  classical
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hev : ∀ᶠ t : ℝ in atTop, ∀ p ∈ F,
      |smoothed g (1/t) p - (slot g p : ℝ)/m| ≤ 2/m := by
    rw [Filter.eventually_all_finset]
    intro p hp
    obtain ⟨j,hj,hju⟩ := hF p hp
    have ht := ((smoothed_scale_limit g j hj hju).sub_const ((slot g p : ℝ)/m)).abs
    have hb : |((slot g p : ℝ)+1/2)/m-(slot g p : ℝ)/m| < 2/m := by
      rw [add_div,add_sub_cancel_left,abs_of_pos (div_pos (by norm_num) hmR)]
      exact div_lt_div_of_pos_right (by norm_num) hmR
    exact (ht.eventually_lt_const hb).mono (fun _ h => h.le)
  obtain ⟨t,ht,hp⟩ := ( (eventually_gt_atTop (0:ℝ)).and hev).exists
  exact ⟨1/t,div_pos zero_lt_one ht,hp⟩
end PlanarHalving.RankCoordinates

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]

lemma finiteMeasure_tendsto_apply {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {E : Set X} (hE : (μ : Measure X) (frontier E) = 0) :
    Tendsto (fun n => μs n E) atTop (𝓝 (μ E)) := by
  by_cases hμ : μ = 0
  · subst μ
    have hmass := h.mass
    have hb (n : ℕ) : μs n E ≤ (μs n).mass := (μs n).apply_mono (subset_univ E)
    simpa using
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass (fun _ => zero_le) hb
  · have hn := FiniteMeasure.tendsto_normalize_of_tendsto h hμ
    have hE' : (μ.normalize : Measure X) (frontier E) = 0 := by
      rw [μ.toMeasure_normalize_eq_of_nonzero hμ,Measure.smul_apply,hE]
      simp
    have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn (by simpa only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_eq_zero] using hE')
    have hh := h.mass.mul ht
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hh

omit [Nonempty X] in
lemma finiteMeasure_tendsto_thickening (μ : FiniteMeasure X) {F : Set X} (hF : IsClosed F)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hp : ∀ n, 0 < r n) :
    Tendsto (fun n => μ (Metric.thickening (r n) F)) atTop (𝓝 (μ F)) := by
  have ht := tendsto_measure_thickening_of_isClosed (μ := (μ : Measure X)) ⟨1,by norm_num,measure_ne_top _ _⟩ hF
  have hr' : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hr,Filter.Eventually.of_forall hp⟩
  have hh := (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure X) F)).comp (ht.comp hr')
  exact hh

lemma cubed_bound_limit_closed
    {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {c d : ℕ → ℝ} {C : ℝ} (hc : Tendsto c atTop (𝓝 C)) (hd : Tendsto d atTop (𝓝 0))
    (hbound : ∀ n U, MeasurableSet U → (lams n U : ℝ)^3 ≤ c n*(μs n U : ℝ)+d n)
    {F : Set X} (hF : IsClosed F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) := by
  obtain ⟨r,hr,hnull⟩ := exists_null_frontiers_thickening ((μ : Measure X)+(lam : Measure X)) F
  have hb (j : ℕ) : (lam (Metric.thickening (r j) F) : ℝ)^3 ≤ C*(μ (Metric.thickening (r j) F) : ℝ) := by
    have hh := (hnull j).2
    rw [Measure.add_apply] at hh
    have hμ' := finiteMeasure_tendsto_apply hμ (add_eq_zero.mp hh).1
    have hlam' := finiteMeasure_tendsto_apply hlam (add_eq_zero.mp hh).2
    have hμR := NNReal.continuous_coe.tendsto _ |>.comp hμ'
    have hlamR := NNReal.continuous_coe.tendsto _ |>.comp hlam'
    have ht := le_of_tendsto_of_tendsto (hlamR.pow 3) ((hc.mul hμR).add hd)
      (Filter.Eventually.of_forall (fun n => hbound n _ Metric.isOpen_thickening.measurableSet))
    simpa only [add_zero] using ht
  have hp : ∀ j, 0 < r j := fun j => (hnull j).1
  have hμR := NNReal.continuous_coe.tendsto _ |>.comp (finiteMeasure_tendsto_thickening μ hF hr hp)
  have hlamR := NNReal.continuous_coe.tendsto _ |>.comp (finiteMeasure_tendsto_thickening lam hF hr hp)
  exact le_of_tendsto_of_tendsto (hlamR.pow 3) (hμR.const_mul C) (Filter.Eventually.of_forall hb)

omit [Nonempty X] in
lemma cubed_bound_of_compact [CompactSpace X]
    (μ lam : FiniteMeasure X) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ K : Set X, IsCompact K → (lam K : ℝ)^3 ≤ C*(μ K : ℝ))
    {F : Set X} (hF : MeasurableSet F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) := by
  have hh (t : ℝ) (ht : t < (lam F : ℝ)) : t^3 ≤ C*(μ F : ℝ) := by
    by_cases ht0 : t < 0
    · exact (show t^3 ≤ 0 by have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) ht0.le; nlinarith).trans (mul_nonneg hC (NNReal.coe_nonneg _))
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      have ht' : ENNReal.ofReal t < (lam : Measure X) F := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal ht0' (measure_ne_top (lam : Measure X) F)]
        exact ht
      obtain ⟨K,hKF,hK,htK⟩ := hF.exists_lt_isCompact ht'
      have htK' : t < (lam K : ℝ) := by
        rwa [ENNReal.ofReal_lt_iff_lt_toReal ht0' (measure_ne_top (lam : Measure X) K)] at htK
      exact (pow_le_pow_left₀ ht0' htK'.le 3).trans ((hbound K hK).trans
        (mul_le_mul_of_nonneg_left (show (μ K : ℝ) ≤ μ F from (NNReal.coe_le_coe.mpr (μ.apply_mono hKF))) hC))
  have ht : Tendsto (fun t : ℝ => t^3) (𝓝[<] (lam F : ℝ)) (𝓝 ((lam F : ℝ)^3)) :=
    ((continuous_pow 3).tendsto _).mono_left inf_le_left
  exact le_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => hh t ht))

lemma cubed_bound_limit [CompactSpace X]
    {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {c d : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hc : Tendsto c atTop (𝓝 C)) (hd : Tendsto d atTop (𝓝 0))
    (hbound : ∀ n U, MeasurableSet U → (lams n U : ℝ)^3 ≤ c n*(μs n U : ℝ)+d n)
    {F : Set X} (hF : MeasurableSet F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) :=
  cubed_bound_of_compact μ lam hC (fun _ hK => cubed_bound_limit_closed hμ hlam hc hd hbound hK.isClosed) hF

end PlanarHalving.Limits

namespace PlanarHalving.Batches
open Set PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

def System.window (S : @System n R k a P) (start len : ℕ) (h : start+len ≤ R) :
    @System n len k a P where
  slope b := S.slope ⟨start+b.val,by omega⟩
  increasing := by
    intro b c hbc
    apply S.increasing
    simpa only [Fin.lt_def] using Nat.add_lt_add_left hbc start
  marks b := S.marks ⟨start+b.val,by omega⟩
  card_marks _ := S.card_marks _
  separates _ := S.separates _
  distance b := S.distance ⟨start+b.val,by omega⟩

lemma System.window_edges (S : @System n R k a P) (start len : ℕ) (h : start+len ≤ R) :
    (S.window start len h).edges ⊆ S.edges := by
  intro e he
  obtain ⟨b,hb,hc⟩ := ((S.window start len h).mem_edges e).mp he
  exact (S.mem_edges e).mpr ⟨⟨start+b.val,by omega⟩,hb,hc⟩

lemma System.window_vertices (S : @System n R k a P) (start len : ℕ) (h : start+len ≤ R) :
    (S.window start len h).vertices ⊆ S.vertices :=
  Finset.union_subset_union (Finset.image_subset_image (S.window_edges start len h))
    (Finset.image_subset_image (S.window_edges start len h))

lemma System.windows_disjoint (S : @System n R k a P)
    {s l t m : ℕ} (h₁ : s+l ≤ R) (h₂ : t+m ≤ R) (h : s+l ≤ t) :
    Disjoint (S.window s l h₁).edges (S.window t m h₂).edges := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨b,hb,hc⟩ := ((S.window s l h₁).mem_edges e).mp he
  obtain ⟨c,hd,he⟩ := ((S.window t m h₂).mem_edges e).mp hf
  have hh := S.batch_unique (b := ⟨s+b.val,by omega⟩) (c := ⟨t+c.val,by omega⟩) ⟨hb,hc⟩ ⟨hd,he⟩
  have hv : s+b.val = t+c.val := congrArg Fin.val hh
  have := b.isLt
  omega

lemma System.windows_slopes (S : @System n R k a P)
    {s l t m : ℕ} (h₁ : s+l ≤ R) (h₂ : t+m ≤ R) (h : s+l ≤ t) :
    (S.window s l h₁).slope (Fin.last l) ≤ (S.window t m h₂).slope 0 := by
  apply S.increasing.monotone
  simpa [Fin.le_def] using h

lemma System.FullGraphs.disjoint_bands (S : @System n R k a P) [NeZero n] [NeZero a]
    {s l t m : ℕ} (h₁ : s+l ≤ R) (h₂ : t+m ≤ R) (h : s+l ≤ t)
    {F G : Finset Point} (A : (S.window s l h₁).FullGraphs F)
    (B : (S.window t m h₂).FullGraphs G) : A.upper < B.lower :=
  A.upper_lt.trans_le (S.windows_slopes h₁ h₂ h) |>.trans B.lower_lt

end PlanarHalving.Batches

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

theorem persistent_mass_zero {ι : Type*} (S : ℕ → Finset ι)
    (lam μ s : ℕ → ι → ℝ) (q : ℕ → ℝ) {L A H U : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hlam0 : ∀ n i, i ∈ S n → 0 ≤ lam n i)
    (hlam1 : ∀ n i, i ∈ S n → lam n i ≤ (q n)⁻¹)
    (hμ0 : ∀ n i, i ∈ S n → 0 ≤ μ n i)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hmass : ∀ n i, i ∈ S n → (lam n i)^3 ≤ A*(s n i)^3*μ n i)
    (hμsum : ∀ n, ∑ i ∈ S n, μ n i ≤ U)
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3))
    (hpartition : ∀ n, L ≤ ∑ i ∈ S n, lam n i) : L = 0 := by
  apply Boundary.mass_eq_zero S lam μ s (fun n i => μ n i/2) (fun _ _ => 0) q
    (L := L) (A := A) (H := H) (B := 0) (B₀ := U/2) (T := 0) (α := 1)
    hL hA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hq hqtop hcard hlam0 hlam1 hμ0 hs0 (by intros; norm_num) hmass
    (by intros; linarith) ?_ (by intros; simp) htail hpartition
  intro n
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (hμsum n) (by norm_num)

end PlanarHalving.Limits

namespace PlanarHalving.PlaneGraph
open Set
variable {n : ℕ} {P : Fin n → Point}

lemma Generic.not_vertex_on_openSegment (hP : Generic P) {i j : Fin n}
    (hij : (P i).1 < (P j).1) (v : Fin n) :
    P v ∉ openSegment ℝ (P i) (P j) := by
  intro hv
  have hbounds := openSegment_horizontal_bounds hij hv
  have hheight := (height_of_mem_openSegment hij.ne hv).2
  have hzero : orient (P i) (P j) (P v) = 0 := by
    rw [orient_eq_proj_diff _ _ _ hij.ne.symm]
    have hh : (P v).2 - slope (P i) (P j) * (P v).1 -
        ((P i).2 - slope (P i) (P j) * (P i).1) = 0 := by
      unfold height at hheight
      nlinarith only [hheight]
    rw [hh,mul_zero]
  have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
  rcases (orient_zero_iff hP.1 hne v).mp hzero with rfl | rfl
  · exact lt_irrefl _ hbounds.1
  · exact lt_irrefl _ hbounds.2

noncomputable def Drawing.exteriorCrossings (D : Drawing P) (E : Finset (Fin n × Fin n)) :
    Finset Point := by
  classical
  exact (Finset.univ.filter (fun w : ↥D.crossings =>
    (w.val.1 ∈ E ∧ w.val.2 ∉ E) ∨ (w.val.2 ∈ E ∧ w.val.1 ∉ E))).image D.crossingPoint

lemma Drawing.exteriorCrossings_not_vertex (D : Drawing P) (hP : Generic P)
    (E : Finset (Fin n × Fin n)) (v : Fin n) : P v ∉ D.exteriorCrossings E := by
  classical
  intro hv
  obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hv
  have hz := (D.crossingPoint_mem w).1
  rw [hw] at hz
  exact Generic.not_vertex_on_openSegment hP (D.right _ (D.crossing_props w).1) v hz

lemma Drawing.exteriorCrossings_unique (D : Drawing P) (hD : D.NoMultiple)
    {E : Finset (Fin n × Fin n)} (hE : E ⊆ D.edges) {z : Point}
    (hz : z ∈ D.exteriorCrossings E) :
    ∃! e, e ∈ E ∧ z ∈ segment ℝ (P e.1) (P e.2) := by
  classical
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  have hw' := (Finset.mem_filter.mp hw).2
  have hp := D.crossing_props w
  have hm := D.crossingPoint_mem w
  have hne : w.val.1 ≠ w.val.2 := fun h => hp.2.2.1.ne (congrArg edgeIndex h)
  have hloc (g : Fin n × Fin n) (hg : g ∈ E)
      (hm : D.crossingPoint w ∈ segment ℝ (P g.1) (P g.2)) :
      g = w.val.1 ∨ g = w.val.2 := by
    by_contra hh
    push Not at hh
    exact hD _ hp.1 _ hp.2.1 hne _ (hE hg) hh.1 hh.2 _
      (D.crossingPoint_mem w).1 (D.crossingPoint_mem w).2 hm
  rcases hw' with hw' | hw'
  · refine ⟨w.val.1,⟨hw'.1,openSegment_subset_segment ℝ _ _ hm.1⟩,?_⟩
    intro g hg
    exact (hloc g hg.1 hg.2).resolve_right (fun h => hw'.2 (h ▸ hg.1))
  · refine ⟨w.val.2,⟨hw'.1,openSegment_subset_segment ℝ _ _ hm.2⟩,?_⟩
    intro g hg
    exact (hloc g hg.1 hg.2).resolve_left (fun h => hw'.2 (h ▸ hg.1))

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

theorem System.window_coordinate (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) (s l : ℕ) (h : s+l ≤ R) (hl : 0 < l) :
    ∃ (G : (S.window s l h).FullGraphs (S.drawing.exteriorCrossings (S.window s l h).edges))
      (ε : ℝ), 0 < ε ∧
      ∀ z ∈ S.drawing.exteriorCrossings (S.window s l h).edges,
        |smoothed G.graph ε z-(slot G.graph z : ℝ)/(a*n)| ≤ 2/(a*n) := by
  let T := S.window s l h
  let F := S.drawing.exteriorCrossings T.edges
  let G := T.fullGraphs hl F (S.drawing.exteriorCrossings_not_vertex hP T.edges)
  have hf (z : Point) (hz : z ∈ F) : ∃! j, G.graph j z.1 = z.2 := by
    obtain ⟨e,he,_⟩ := S.drawing.exteriorCrossings_unique (S.drawing.noMultiple_of_generic hP)
      (S.window_edges s l h) hz
    refine ⟨finProdFinEquiv (T.convexOwner e),G.edge e he.1 z he.2,?_⟩
    intro j hj
    apply G.unique_incidence T (fun q hq e he f hf hqe hqf => ?_) hz hj (G.edge e he.1 z he.2)
    obtain ⟨b,_,hb⟩ := S.drawing.exteriorCrossings_unique (S.drawing.noMultiple_of_generic hP)
      (S.window_edges s l h) hq
    exact (hb e ⟨he,hqe⟩).trans (hb f ⟨hf,hqf⟩).symm
  obtain ⟨ε,hε,herr⟩ := exists_smoothing_slot_error (Nat.mul_pos (NeZero.pos a) (NeZero.pos n)) G.graph F hf
  exact ⟨G,ε,hε,by simpa only [Nat.cast_mul] using herr⟩

end PlanarHalving.Batches

end OAI
