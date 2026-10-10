import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.InteriorScalar

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open Set Filter Topology TopologicalSpace Metric

namespace CannonContinuumLimit

lemma connected_limit {X : Type*} [MetricSpace X]
    {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K atTop (𝓝 L)) (hc : ∀ n, IsConnected (K n : Set X)) :
    IsConnected (L : Set X) := by
  refine ⟨L.nonempty, ?_⟩
  intro U V hU hV hcover hLU hLV
  by_contra hn
  obtain ⟨A, B, hA, hB, hAU, hBV, hAB⟩ :=
    L.isCompact.binary_compact_cover hU hV hcover
  have hdis : Disjoint A B := by
    rw [disjoint_left]
    intro x hxA hxB
    exact hn ⟨x, by rw [hAB]; exact Or.inl hxA, hAU hxA, hBV hxB⟩
  obtain ⟨U', V', hU', hV', hAU', hBV', hdis'⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hA hB hB.isClosed hdis
  have hc' : (L : Set X) ⊆ U' ∪ V' := by
    rw [hAB]
    exact union_subset_union hAU' hBV'
  have hLU' : ((L : Set X) ∩ U').Nonempty := by
    obtain ⟨x,hxL,hxU⟩ := hLU
    have hxA : x ∈ A := by
      rcases (show x ∈ A ∪ B by rwa [← hAB]) with h | h
      · exact h
      · exact False.elim (hn ⟨x,hxL,hxU,hBV h⟩)
    exact ⟨x,hxL,hAU' hxA⟩
  have hLV' : ((L : Set X) ∩ V').Nonempty := by
    obtain ⟨x,hxL,hxV⟩ := hLV
    have hxB : x ∈ B := by
      rcases (show x ∈ A ∪ B by rwa [← hAB]) with h | h
      · exact False.elim (hn ⟨x,hxL,hAU h,hxV⟩)
      · exact h
    exact ⟨x,hxL,hBV' hxB⟩
  have he₁ : ∀ᶠ n in atTop, (K n : Set X) ⊆ U' ∪ V' := hlim ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU'.union hV')).mem_nhds hc')
  have he₂ : ∀ᶠ n in atTop, ((K n : Set X) ∩ U').Nonempty := hlim ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU').mem_nhds hLU')
  have he₃ : ∀ᶠ n in atTop, ((K n : Set X) ∩ V').Nonempty := hlim ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV').mem_nhds hLV')
  obtain ⟨n,hn₁,hn₂,hn₃⟩ := (he₁.and (he₂.and he₃)).exists
  obtain ⟨x,_,hxU,hxV⟩ := (hc n).2 U' V' hU' hV' hn₁ hn₂ hn₃
  exact disjoint_left.mp hdis' hxU hxV

lemma diam_le_add_dist {X : Type*} [MetricSpace X] (K L : NonemptyCompacts X) :
    diam (K : Set X) ≤ diam (L : Set X) + 2 * dist K L := by
  apply diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨x',hx',hxx'⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  obtain ⟨y',hy',hyy'⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty y
  have hfin : hausdorffEDist (K : Set X) L ≠ ⊤ := edist_ne_top K L
  have hxD := infDist_le_hausdorffDist_of_mem hx hfin
  have hyD := infDist_le_hausdorffDist_of_mem hy hfin
  rw [hxx'] at hxD
  rw [hyy'] at hyD
  have hxy := dist_le_diam_of_mem L.isCompact.isBounded hx' hy'
  have htri := dist_triangle4 x x' y' y
  rw [dist_comm y' y] at htri
  change dist x x' ≤ dist K L at hxD
  change dist y y' ≤ dist K L at hyD
  linarith

lemma diameter_limit {X : Type*} [MetricSpace X]
    {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K atTop (𝓝 L)) {d : ℝ}
    (hd : ∀ᶠ n in atTop, d ≤ diam (K n : Set X)) :
    d ≤ diam (L : Set X) := by
  have ht : Tendsto (fun n => diam (L : Set X) + 2 * dist (K n) L)
      atTop (𝓝 (diam (L : Set X))) := by
    have hdist : Tendsto (fun n => dist (K n) L) atTop (𝓝 0) := by
      simpa using hlim.dist (tendsto_const_nhds (x := L))
    simpa using (tendsto_const_nhds (x := diam (L : Set X))).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hdist)
  exact ge_of_tendsto ht (hd.mono (fun n hn => hn.trans (diam_le_add_dist (K n) L)))

lemma approximating_points {X : Type*} [MetricSpace X]
    {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K atTop (𝓝 L)) {x : X} (hx : x ∈ L) :
    ∃ y : ℕ → X, (∀ n, y n ∈ K n) ∧ Tendsto y atTop (𝓝 x) := by
  choose y hy hdist using fun n => (K n).isCompact.exists_infDist_eq_dist (K n).nonempty x
  refine ⟨y,hy,?_⟩
  have ht := (NonemptyCompacts.lipschitz_infDist_const x).continuous.tendsto L |>.comp hlim
  rw [infDist_zero_of_mem hx] at ht
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, hdist, dist_comm] using ht

lemma level_limit {X : Type*} [MetricSpace X]
    {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K atTop (𝓝 L)) {U : Set X} (hU : IsOpen U)
    {f : ℕ → X → ℝ} {u : X → ℝ} (hcont : ContinuousOn u U)
    (hf : TendstoLocallyUniformlyOn f u atTop U) {t : ℝ}
    (hlevel : ∀ n, ∀ x ∈ K n, f n x = t) :
    ∀ x ∈ (L : Set X) ∩ U, u x = t := by
  intro x hx
  obtain ⟨y,hy,ht⟩ := approximating_points hlim hx.1
  have ht' : Tendsto y atTop (𝓝[U] x) := by rwa [hU.nhdsWithin_eq hx.2]
  have h := hf.tendsto_comp (hcont x hx.2) hx.2 ht'
  have he : (fun n => f n (y n)) = fun _ => t := funext (fun n => hlevel n (y n) (hy n))
  rw [he] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds)

lemma closed_meeting_limit {X : Type*} [MetricSpace X]
    {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K atTop (𝓝 L)) {P : Set X} (hP : IsClosed P)
    (hmeet : ∀ᶠ n in atTop, ((K n : Set X) ∩ P).Nonempty) :
    ((L : Set X) ∩ P).Nonempty :=
  (NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hP).mem_of_tendsto hlim hmeet

theorem continuum_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    (K : ℕ → NonemptyCompacts X) (hc : ∀ n, IsConnected (K n : Set X))
    {d : ℝ} (hd : ∀ n, d ≤ diam (K n : Set X)) :
    ∃ L : NonemptyCompacts X, IsConnected (L : Set X) ∧ d ≤ diam (L : Set X) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (K ∘ φ) atTop (𝓝 L) := by
  obtain ⟨L,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq K
  exact ⟨L,connected_limit ht (fun n => hc (φ n)),
    diameter_limit ht (Eventually.of_forall (fun n => hd (φ n))),φ,hφ,ht⟩

end CannonContinuumLimit

namespace CannonContinuumLimit

open Set Metric Filter Topology

theorem domain_level_limit {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    {U : Set X} (hU : IsOpen U) {K : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hK : Tendsto K atTop (𝓝 L)) {f : ℕ → C(U,ℝ)} {u : C(U,ℝ)}
    (hf : Tendsto f atTop (𝓝 u)) {t : ℝ}
    (hlevel : ∀ n (x : U), x.val ∈ K n → f n x = t) :
    ∀ x : U, x.val ∈ L → u x = t := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  intro x hx
  obtain ⟨y,hy,hyt⟩ := approximating_points hK hx
  have hyU : ∀ᶠ n in atTop, y n ∈ U := hyt.eventually (hU.mem_nhds x.property)
  let ys : ℕ → U := fun n => if h : y n ∈ U then ⟨y n,h⟩ else x
  have hys : Tendsto ys atTop (𝓝 x) := by
    apply tendsto_subtype_rng.mpr
    apply Tendsto.congr' _ hyt
    filter_upwards [hyU] with n hn
    simp [ys,hn]
  have ht : Tendsto (fun n => f n (ys n)) atTop (𝓝 (u x)) :=
    continuous_eval.tendsto (u,x) |>.comp (hf.prodMk_nhds hys)
  have he : (fun n => f n (ys n)) =ᶠ[atTop] fun _ => t := by
    filter_upwards [hyU] with n hn
    simp only [ys,dite_eq_left hn]
    exact hlevel n ⟨y n,hn⟩ (hy n)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

theorem straddling_continua_limit {X : Type*} [MetricSpace X] [CompactSpace X]
    {U : Set X} (hU : IsOpen U) (Q : Set X) (hQ : IsClosed Q)
    (K : ℕ → NonemptyCompacts X) (hc : ∀ n, IsConnected (K n : Set X))
    (hsub : ∀ n, (K n : Set X) ⊆ Q) {d : ℝ} (hd : ∀ n, d ≤ diam (K n : Set X))
    {f : ℕ → C(U,ℝ)} {u : C(U,ℝ)} (hf : Tendsto f atTop (𝓝 u)) {t : ℝ}
    (hlevel : ∀ n (x : U), x.val ∈ K n → f n x = t)
    (hhit : ∀ n {x y : U} (p : Path x y), f n x < t → t < f n y →
      ∃ s, (p s).val ∈ K n) :
    ∃ L : NonemptyCompacts X, IsConnected (L : Set X) ∧ (L : Set X) ⊆ Q ∧
      d ≤ diam (L : Set X) ∧ (∀ x : U, x.val ∈ L → u x = t) ∧
      ∀ {x y : U} (p : Path x y), u x < t → t < u y → ∃ s, (p s).val ∈ L := by
  obtain ⟨L,hLc,hLd,ψ,hψ,hKL⟩ := continuum_subsequence K hc hd
  have hLQ : (L : Set X) ⊆ Q := by
    intro x hx
    obtain ⟨y,hy,hyt⟩ := approximating_points hKL hx
    exact hQ.mem_of_tendsto hyt (Eventually.of_forall (fun n => hsub _ (hy n)))
  refine ⟨L,hLc,hLQ,hLd,domain_level_limit hU hKL (hf.comp hψ.tendsto_atTop)
    (fun n x hx => hlevel _ x hx),?_⟩
  intro x y p hx hy
  let P : Set X := range (fun s => (p s).val)
  have hPc : IsCompact P := isCompact_range (continuous_subtype_val.comp p.continuous)
  have hxev : ∀ᶠ n in atTop, f (ψ n) x < t :=
    ((continuous_eval_const x).tendsto u |>.comp (hf.comp hψ.tendsto_atTop)).eventually_lt_const hx
  have hyev : ∀ᶠ n in atTop, t < f (ψ n) y :=
    ((continuous_eval_const y).tendsto u |>.comp (hf.comp hψ.tendsto_atTop)).eventually_const_lt hy
  have hmeet : ∀ᶠ n in atTop, ((K (ψ n) : Set X) ∩ P).Nonempty := by
    filter_upwards [hxev,hyev] with n hn₁ hn₂
    obtain ⟨s,hs⟩ := hhit (ψ n) p hn₁ hn₂
    exact ⟨(p s).val,hs,⟨s,rfl⟩⟩
  obtain ⟨z,hz,⟨s,hs⟩⟩ := closed_meeting_limit hKL hPc.isClosed hmeet
  refine ⟨s,?_⟩
  cases hs
  exact hz

end CannonContinuumLimit

namespace CannonApprox

open CannonGrid CannonChart CannonLevel CannonContinuumLimit
open Set Metric Filter Topology TopologicalSpace

theorem constructed_scalar_continua {X : Type*} [MetricSpace X] [CompactSpace X]
    (e : Square → X) (he : IsEmbedding e)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X) (r : ℕ → ℝ)
    (ρ : ∀ n, ι n → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (u : C(interior (range e),ℝ))
    (hf : Tendsto (fun n => interiorScalar e he (p n) (r n)
        (ρ n) (hρ n) (hadm n) (m n) (hm n)) atTop (𝓝 u)) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ t ∈ Ioo (0:ℝ) 1,
      ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ A ⊆ e '' centralRectangle ∧
        d₁ ≤ diam A ∧ (∀ x : interior (range e), x.val ∈ A → u x = t) ∧
        ∀ {x y : interior (range e)} (p : Path x y),
          u x < t → t < u y → ∃ s, (p s).val ∈ A := by
  classical
  obtain ⟨d₁,hd₁,hdiam⟩ := exists_chart_lateral_diameter e he
  refine ⟨d₁,hd₁,fun t ht => ?_⟩
  choose A hAc hAconn hAQ hAd hAlevel hAhit using fun n =>
    scalar_ambient_level e he (fun i => e ⁻¹' ball (p n i) (2*r n))
      (ρ n) (hρ n) (hadm n) (m n) (hm n) d₁ hdiam t ht
  let K : ℕ → NonemptyCompacts X := fun n => ⟨⟨A n,hAc n⟩,(hAconn n).1⟩
  have hcentral : IsCompact centralRectangle :=
    (isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)).isCompact
  have hQ : IsClosed (e '' centralRectangle) :=
    (hcentral.image he.continuous).isClosed
  have hhit (n : ℕ) {x y : interior (range e)} (q : Path x y)
      (hx : interiorScalar e he (p n) (r n) (ρ n) (hρ n) (hadm n) (m n) (hm n) x < t)
      (hy : t < interiorScalar e he (p n) (r n) (ρ n) (hρ n) (hadm n) (m n) (hm n) y) :
      ∃ s, (q s).val ∈ K n := by
    obtain ⟨a,ha⟩ := interior_subset x.property
    obtain ⟨b,hb⟩ := interior_subset y.property
    let q' : Path (e a) (e b) := (q.map continuous_subtype_val).cast ha hb
    have hx' : scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n) a < t := by
      change extend e _ x.val < t at hx
      rw [← ha,extend_apply e he.injective] at hx
      exact hx
    have hy' : t < scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n) b := by
      change t < extend e _ y.val at hy
      rw [← hb,extend_apply e he.injective] at hy
      exact hy
    exact hAhit n q' (fun s => interior_subset (q s).property) hx' hy'
  obtain ⟨L,hLc,hLQ,hLd,hLl,hLhit⟩ := straddling_continua_limit isOpen_interior
    (e '' centralRectangle) hQ K hAconn hAQ hAd hf (fun n x hx => hAlevel n x hx) hhit
  exact ⟨L,L.isCompact,hLc,hLQ,hLd,hLl,hLhit⟩

end CannonApprox

namespace CannonMeasureOscillation

open CannonScalarLimit Metric

lemma inverse_geometric_near {a s : ℝ} (ha : 1 < a) (l₀ : ℕ) (hs : 0 < s)
    (hsmall : s ≤ (a^l₀)⁻¹) :
    ∃ l : ℕ, l₀ ≤ l ∧ s ≤ (a^l)⁻¹ ∧ (a^l)⁻¹ < a*s := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hsone : s ≤ 1 := hsmall.trans (inv_le_one_of_one_le₀ (one_le_pow₀ ha.le))
  obtain ⟨l,hl₁,hl₂⟩ := exists_nat_pow_near_of_lt_one hs hsone
    (inv_pos.mpr hap) (inv_lt_one_of_one_lt₀ ha)
  have hl₀ : l₀ ≤ l := by
    by_contra hn
    have hle : l+1 ≤ l₀ := by omega
    have hh := pow_le_pow_of_le_one (inv_nonneg.mpr hap.le)
      (inv_lt_one_of_one_lt₀ ha).le hle
    rw [inv_pow,inv_pow] at hh
    rw [inv_pow] at hl₁
    exact (hl₁.trans_le (hsmall.trans hh)).false
  refine ⟨l,hl₀,by simpa only [inv_pow] using hl₂,?_⟩
  have hh := mul_lt_mul_of_pos_right hl₁ hap
  rw [pow_succ,inv_pow] at hh
  simpa only [mul_assoc,inv_mul_cancel₀ hap.ne',mul_one,mul_comm s a] using hh

lemma osc_sq_le_of_pairwise {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A)
    {E : ℝ} (hE : 0 ≤ E)
    (hpair : ∀ x ∈ A, ∀ y ∈ A, (f x-f y)^2 ≤ E) : (osc A f)^2 ≤ E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simpa [osc] using hE
  obtain ⟨x,hx,heqx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,heqy⟩ := (hA.image hf).sInf_mem (hne.image f)
  simpa only [osc,← heqx,← heqy] using hpair x hx y hy

lemma compact_subtype_closedBall {X : Type*} [MetricSpace X] [CompactSpace X]
    {U : Set X} {o : X} {s : ℝ} (hsub : closedBall o s ⊆ U) :
    IsCompact (Subtype.val ⁻¹' closedBall o s : Set U) := by
  apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
  have he : Subtype.val '' (Subtype.val ⁻¹' closedBall o s : Set U) = closedBall o s := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z,hsub hz⟩,hz,rfl⟩
  rw [he]
  exact isCompact_closedBall o s

theorem annular_to_measure {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X) (hU : IsOpen U)
    (f : ℕ → C(U,ℝ)) (u : C(U,ℝ)) (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a L E : ℝ) (ha : 1 < a) (hL : 0 < L) (hE : 0 ≤ E)
    (hann : ∀ K : Set X, IsCompact K → K ⊆ U → ∃ l₀ m₀ : ℕ,
      ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K, ∀ x y : U,
      dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ E*(μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ))
    (hf : Tendsto f atTop (𝓝 u)) (hμ : Tendsto μ atTop (𝓝 ν)) :
    ∀ K : Set X, IsCompact K → K ⊆ U → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ o ∈ K,
        closedBall o s ⊆ U ∧
        (osc (Subtype.val ⁻¹' closedBall o s : Set U) u)^2 ≤
          E*(ν (closedBall o ((8*a*L)*s)) : ℝ) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  intro K hK hKU
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hap : 0 < a := zero_lt_one.trans ha
  have hden : 0 < 2*L := by positivity
  let s₀ := min (δ/2) ((a^l₀)⁻¹/(2*L))
  have hs₀ : 0 < s₀ := lt_min (by positivity) (by positivity)
  refine ⟨s₀,hs₀,fun s hs hss o ho => ?_⟩
  have hsδ : s < δ := lt_of_le_of_lt (hss.trans (min_le_left _ _)) (by linarith)
  have hB : closedBall o s ⊆ U := by
    intro z hz
    exact hδU (mem_thickening_iff.mpr ⟨o,ho,(mem_closedBall.mp hz).trans_lt hsδ⟩)
  have hsR : 2*L*s ≤ (a^l₀)⁻¹ := by
    have hh := (le_div_iff₀ hden).mp (hss.trans (min_le_right _ _))
    nlinarith
  obtain ⟨l,hl,hl₁,hl₂⟩ := inverse_geometric_near ha l₀ (mul_pos hden hs) hsR
  have hsinner : s ≤ (a^l)⁻¹/(2*L) := (le_div_iff₀ hden).mpr (by nlinarith [hl₁])
  have hA : IsCompact (Subtype.val ⁻¹' closedBall o s : Set U) := compact_subtype_closedBall hB
  refine ⟨hB,?_⟩
  apply oscillation_measure_limit hA isClosed_closedBall hf hμ hE
  filter_upwards [hN.eventually (eventually_ge_atTop (l+m₀))] with n hn
  apply osc_sq_le_of_pairwise (f n).continuous hA (mul_nonneg hE (NNReal.coe_nonneg _))
  intro x hx y hy
  have hh := hann l hl n hn o ho x y
    ((mem_closedBall.mp hx).trans hsinner) ((mem_closedBall.mp hy).trans hsinner)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hE
  exact_mod_cast (μ n).apply_mono (show
    {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} ⊆
      closedBall o ((8*a*L)*s) from fun z hz =>
    mem_closedBall.mpr (hz.2.trans (by nlinarith [hl₂])))

end CannonMeasureOscillation

end
end
end
end
end
end
end
end
end

end OAI
