import OAI.Geometry.PinnedDistances.ExtremalCore

namespace OAI

universe u1 u2

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

/-- Retain a specified family of the original fibers, restricted to D.
    This never alters a source or creates a new distance coincidence. -/
def retained (D : Finset V) (Q : I → Prop) [DecidablePred Q] : Fibers V I where
  source := G.source
  targets e := if Q e then G.targets e ∩ D else ∅
  no_loop e := by
    split_ifs
    · exact fun h => G.no_loop e (Finset.mem_inter.mp h).1
    · simp
  disjoint e f hef hs := by
    apply Finset.disjoint_left.mpr
    intro y hy hf
    by_cases he : Q e <;> by_cases hh : Q f
    · simp only [he,hh,ite_eq_left] at hy hf
      exact (Finset.disjoint_left.mp (G.disjoint e f hef hs))
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hf).1
    all_goals simp [he,hh] at hy hf

lemma retained_card (D : Finset V) (Q : I → Prop) [DecidablePred Q] :
    (((G.retained D Q).edgeSet (-1) D).card : ℝ) =
      ∑ e, if Q e ∧ G.source e ∈ D then (G.size D e : ℝ) else 0 := by
  rw [edgeSet_card]
  apply Finset.sum_congr rfl
  intro e _
  have hsize : (G.retained D Q).size D e = if Q e then G.size D e else 0 := by
    by_cases hq : Q e <;> simp [size,retained,hq]
  have ha : (G.retained D Q).active (-1) D e ↔ G.source e ∈ D := by
    change (G.source e ∈ D ∧ (-1:ℝ)<((G.retained D Q).size D e : ℝ)) ↔ _
    have hh : (-1:ℝ)<((G.retained D Q).size D e : ℝ) := by have hh := Nat.cast_nonneg (α:=ℝ) ((G.retained D Q).size D e); linarith
    simp [hh]
  simp only [ha,hsize]
  by_cases hq : Q e <;> by_cases hs : G.source e ∈ D <;> simp [hq,hs]

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators

def heavyFiber (P : Finset Plane) (s K lam : ℝ) (C D : Finset P)
    (e : fiberIndices P s) : Prop :=
  (planarFibers P s).active K C e ∧
    lam*((planarFibers P s).size C e : ℝ) ≤ (planarFibers P s).size D e

instance (P : Finset Plane) (s K lam : ℝ) (C D : Finset P) :
    DecidablePred (heavyFiber P s K lam C D) := Classical.decPred _

lemma heavySubset_edge_rich (P : Finset Plane) (s K lam r : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hK : (D.card : ℝ)^r ≤ lam*K) (x y : P)
    (hxy : ((planarFibers P s).retained D (heavyFiber P s K lam C D)).edge (-1) D x y) :
    (x.val,y.val) ∈ richPairs (planeSubset P D) r := by
  obtain ⟨e,ha,hsrc,hy⟩ := hxy
  have hxD : x ∈ D := hsrc ▸ ha.1
  have hyD := (Finset.mem_inter.mp hy).2
  have hyT := (Finset.mem_inter.mp hy).1
  change y ∈ (if heavyFiber P s K lam C D e then (planarFibers P s).targets e ∩ D else ∅) at hyT
  split_ifs at hyT with he
  · obtain ⟨hactive,hheavy⟩ := he
    have hsz : (D.card : ℝ)^r ≤ ((planarFibers P s).size D e : ℝ) :=
      hK.trans ((mul_le_mul_of_nonneg_left (le_of_lt hactive.2) hlam).trans hheavy)
    have hyT' := (Finset.mem_inter.mp hyT).1
    have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
    have hne : x.val ≠ y.val := by
      intro hh
      have hd := (planar_target_iff P s e y).mp hyT'
      rw [hsrc',hh,dist_self] at hd
      exact (index_radius_pos P s e).ne hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hxD,rfl⟩,
      Finset.mem_image.mpr ⟨y,hyD,rfl⟩⟩,hne,?_⟩
    rw [planeSubset_card]
    have hc := Finset.card_le_card (restricted_targets_subset P s D e y hyT')
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hsrc'] at hc
    exact hsz.trans (by exact_mod_cast hc)
  · simp at hyT

/-- The exact finite counting step underlying both uniform subset estimates
    for the rich-pair graph. Each ordered pair is counted only once. -/
theorem heavySubset_count (P : Finset Plane) (s K lam r : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hK : (D.card : ℝ)^r ≤ lam*K) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) ≤
      (richPairs (planeSubset P D) r).card := by
  rw [← (planarFibers P s).retained_card]
  suffices h : (((planarFibers P s).retained D (heavyFiber P s K lam C D)).edgeSet (-1) D).card ≤
      (richPairs (planeSubset P D) r).card by exact_mod_cast h
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨xy,he,rfl⟩ := Finset.mem_image.mp hz
  exact heavySubset_edge_rich P s K lam r C D hlam hK xy.1 xy.2 (Finset.mem_filter.mp he).2

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

def Theta (s : ℝ) : ℝ := limsup (fun n : ℕ => F n s) atTop

lemma F_bdd (s : ℝ) : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => F n s) :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => F_le_one n s))
lemma F_cobdd (s : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => F n s) :=
  isCoboundedUnder_le_of_le atTop (fun n => F_nonneg n s)

lemma Theta_nonneg (s : ℝ) : 0 ≤ Theta s := by
  have hh := limsup_le_limsup (f:=atTop) (u:=fun _ : ℕ => (0:ℝ)) (v:=fun n => F n s)
    (Eventually.of_forall (fun n => F_nonneg n s)) (isCoboundedUnder_le_of_le atTop (fun _ => le_refl (0:ℝ))) (F_bdd s)
  change 0 ≤ limsup (fun n : ℕ => F n s) atTop
  simpa only [limsup_const] using hh

lemma Theta_le_one (s : ℝ) : Theta s ≤ 1 :=
  limsup_le_of_le (F_cobdd s) (Eventually.of_forall (fun n => F_le_one n s))

lemma Theta_antitone : Antitone Theta := by
  intro s t hst
  exact limsup_le_limsup (Eventually.of_forall (fun n => F_antitone n hst)) (F_cobdd t) (F_bdd s)

lemma Theta_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : Theta s=0 := by
  simp [Theta,F_eq_zero_of_one_le _ hs]

lemma tendsto_F_of_Theta_zero {s : ℝ} (hs : Theta s=0) : Tendsto (fun n : ℕ => F n s) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (F_nonneg n s))
  · intro a ha
    exact eventually_lt_of_limsup_lt (by change Theta s < a; simpa [hs] using ha) (F_bdd s)

def criticalExponent : ℝ := sSup {s : ℝ | 0 < s ∧ 0 < Theta s}

lemma positive_exponents_bdd : BddAbove {s : ℝ | 0 < s ∧ 0 < Theta s} := by
  refine ⟨1,?_⟩
  intro s hs
  by_contra hn
  have hz := Theta_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hn))
  linarith [hs.2]

lemma failed_main_nonempty (h : ¬ MainStatement) : {s : ℝ | 0 < s ∧ 0 < Theta s}.Nonempty := by
  by_contra hn
  apply h
  intro s hs
  apply tendsto_F_of_Theta_zero
  have hnp : ¬0 < Theta s := fun hp => hn ⟨s,hs,hp⟩
  exact le_antisymm (le_of_not_gt hnp) (Theta_nonneg s)

lemma critical_pos (h : ¬ MainStatement) : 0 < criticalExponent := by
  obtain ⟨s,hs,hθ⟩ := failed_main_nonempty h
  exact hs.trans_le (le_csSup positive_exponents_bdd ⟨hs,hθ⟩)

lemma critical_le_one (h : ¬ MainStatement) : criticalExponent ≤ 1 :=
  csSup_le (failed_main_nonempty h) (fun s hs => by
    by_contra hn
    have hz := Theta_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hn))
    linarith [hs.2])

lemma Theta_pos_below_critical (h : ¬ MainStatement) {s : ℝ} (hs : s < criticalExponent) : 0 < Theta s := by
  obtain ⟨t,ht,hst⟩ := exists_lt_of_lt_csSup (failed_main_nonempty h) hs
  exact ht.2.trans_le (Theta_antitone (le_of_lt hst))

lemma Theta_zero_above_critical (h : ¬ MainStatement) {s : ℝ} (hs : criticalExponent < s) : Theta s=0 := by
  apply le_antisymm _ (Theta_nonneg s)
  by_contra hn
  have hp : 0 < Theta s := lt_of_not_ge hn
  have hs0 := (critical_pos h).trans hs
  have hh : s ≤ criticalExponent := le_csSup positive_exponents_bdd ⟨hs0,hp⟩
  linarith

/-- A fixed exponent regime obtained from failure of the uniform multiplicity limit. -/

theorem extremal_parameters (h : ¬ MainStatement) :
    ∃ c s γ : ℝ, 0 < c ∧ c < criticalExponent/3 ∧
      max c ((1-c)*criticalExponent) < s ∧ s < criticalExponent ∧
      c < γ ∧ γ < s ∧ ContinuousAt Theta s ∧ 0 < Theta s := by
  let c := criticalExponent/4
  have hp := critical_pos h
  have h1 := critical_le_one h
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hc3 : c < criticalExponent/3 := by dsimp [c]; linarith
  have hcm : c < criticalExponent := by dsimp [c]; linarith
  have hm : (1-c)*criticalExponent < criticalExponent := by nlinarith
  have hmax : max c ((1-c)*criticalExponent) < criticalExponent := max_lt hcm hm
  have hd := (Theta_antitone.countable_not_continuousAt).dense_compl ℝ
  obtain ⟨s,hs,hr⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hmax)
  have hcs : c < s := (le_max_left _ _).trans_lt hr.1
  refine ⟨c,s,(c+s)/2,hc0,hc3,hr.1,hr.2,?_,?_,?_,Theta_pos_below_critical h hr.2⟩
  · linarith
  · linarith
  · simpa only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_not] using hs

lemma extremal_subsequence (s : ℝ) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto (fun i => F (N i) s) atTop (𝓝 (Theta s)) := by
  obtain ⟨N,hN,hT⟩ := exists_seq_tendsto_limsup (F_cobdd s) (F_bdd s)
  exact ⟨N,hT,hN⟩

/-- The epsilon-uniform extremal tail bound. The lower cutoff may vary arbitrarily
    provided it tends to infinity. -/
lemma extremal_tail {s : ℝ} (hs : ContinuousAt Theta s) {r : ℕ → ℝ} {M : ℕ → ℕ}
    (hr : Tendsto r atTop (𝓝 s)) (hM : Tendsto M atTop atTop) :
    ∀ ε > 0, ∀ᶠ i in atTop, ∀ m : ℕ, M i ≤ m → F m (r i) ≤ Theta s+ε := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hs (ε/2) (by linarith)
  let t := s-δ/2
  have ht : t < s := by dsimp [t]; linarith
  have hdist : dist t s < δ := by
    rw [Real.dist_eq,abs_of_neg (by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  have hΘ : Theta t < Theta s+ε/2 := by
    have hh := (abs_lt.mp (show |Theta t-Theta s| < ε/2 from by simpa only [Real.dist_eq] using hcont hdist)).2
    linarith
  have hev : ∀ᶠ m : ℕ in atTop, F m t < Theta s+ε :=
    eventually_lt_of_limsup_lt (lt_trans hΘ (by linarith)) (F_bdd t)
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp hev
  filter_upwards [hr.eventually_const_lt ht,(tendsto_atTop.mp hM) m₀] with i hi hmi
  intro m hm
  exact (F_antitone m (le_of_lt hi)).trans (le_of_lt (hm₀ m (hmi.trans hm)))

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

def cutoff (s : ℝ) (N : ℕ) : ℝ := (N : ℝ)^s/Real.log N

lemma eventual_power_below_cutoff {s r : ℝ} (hrs : r < s) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^r ≤ cutoff s N := by
  have ho := (isLittleO_log_rpow_atTop (sub_pos.mpr hrs)).bound (show (0:ℝ)<1 by norm_num)
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually ho,hn.eventually (eventually_gt_atTop 1)] with N hN hp
  have hlog : 0 < Real.log N := Real.log_pos hp
  have hpow : 0 ≤ (N : ℝ)^(s-r) := Real.rpow_nonneg (by linarith) _
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog.le,abs_of_nonneg hpow,one_mul] at hN
  unfold cutoff
  apply (le_div_iff₀ hlog).mpr
  calc
    (N : ℝ)^r*Real.log N ≤ (N : ℝ)^r*(N : ℝ)^(s-r) :=
      mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg (by linarith) _)
    _ = (N : ℝ)^s := by rw [← Real.rpow_add (by linarith : (0:ℝ)<N)]; congr 1; ring

lemma eventual_cutoff_loss (s η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ cutoff s N ∧ cutoff s N < (N : ℝ)^s ∧
      cutoff s N ≤ (η/8)*(N : ℝ)^s := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  filter_upwards [hl.eventually (eventually_gt_atTop (max 1 (8/η))),
    hn.eventually (eventually_gt_atTop 1)] with N hlog hN
  have hlog1 : 1 < Real.log N := (le_max_left _ _).trans_lt hlog
  have hlogη : 8/η < Real.log N := (le_max_right _ _).trans_lt hlog
  have hp : 0 < (N : ℝ)^s := Real.rpow_pos_of_pos (by linarith) _
  have hi : (1:ℝ)/Real.log N ≤ η/8 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log N)).mpr
    have hh : 8 < Real.log N*η := (div_lt_iff₀ hη).mp hlogη
    nlinarith
  refine ⟨div_nonneg hp.le (by linarith),?_,?_⟩
  · exact (div_lt_iff₀ (by linarith : 0 < Real.log N)).mpr (by nlinarith)
  · unfold cutoff
    calc
      (N : ℝ)^s/Real.log N = (1/Real.log N)*(N : ℝ)^s := by ring
      _ ≤ (η/8)*(N : ℝ)^s := mul_le_mul_of_nonneg_right hi hp.le

lemma continuous_left_tail {s γ ε : ℝ} (hγ : γ < s) (hε : 0 < ε)
    (hs : ContinuousAt Theta s) :
    ∃ r : ℝ, γ < r ∧ r < s ∧ ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → F m r ≤ Theta s+ε := by
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hs (ε/2) (by linarith)
  obtain ⟨r,hrlo,hrhi⟩ := exists_between (show max γ (s-δ) < s by exact max_lt hγ (by linarith))
  have hγr : γ < r := (le_max_left _ _).trans_lt hrlo
  have hdist : dist r s < δ := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hrhi)]
    have hh := (le_max_right γ (s-δ)).trans_lt hrlo
    linarith
  have ht : Theta r < Theta s+ε := by
    have hh := (abs_lt.mp (show |Theta r-Theta s| < ε/2 from by simpa only [Real.dist_eq] using hcont hdist)).2
    linarith
  obtain ⟨m₁,hm⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt ht (F_bdd r))
  exact ⟨r,hγr,hrhi,m₁,fun m hm₁ => (hm m hm₁).le⟩

lemma half_boundary (N : ℕ) (hN : 4 ≤ N) :
    let m₀ := (N+1)/2
    2 ≤ m₀ ∧ m₀ < N ∧
      (m₀ : ℝ)*((m₀ : ℝ)-1) ≤ (N : ℝ)*((N : ℝ)-1)/2 := by
  dsimp
  have hm : 2 ≤ (N+1)/2 := by omega
  have hlt : (N+1)/2 < N := by omega
  refine ⟨hm,hlt,?_⟩
  have h2 : 2*((N+1)/2) ≤ N+1 := by omega
  have h2R : (2:ℝ)*((N+1)/2 : ℕ) ≤ (N : ℝ)+1 := by exact_mod_cast h2
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hmR : (2:ℝ) ≤ ((N+1)/2 : ℕ) := by exact_mod_cast hm
  nlinarith

/-- Actual core configurations at arbitrarily small density error and arbitrarily
    large cardinality. No field or position assumptions are introduced. -/
theorem arbitrarily_large_core {s γ : ℝ} (hγ : 0 < γ) (hγs : γ < s)
    (hs : ContinuousAt Theta s) (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M < C.card ∧
      (P.card+1)/2 < C.card ∧ (C.card : ℝ)^γ ≤ cutoff s P.card ∧
      (Theta s-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ ((planarFibers P s).edgeSet (cutoff s P.card) C).card ∧
      (((planarFibers P s).edgeSet (cutoff s P.card) C).card : ℝ) ≤
        (Theta s+η/8)*(C.card : ℝ)*((C.card : ℝ)-1) ∧
      (∀ x ∈ C, 2*(Theta s-η)*((C.card : ℝ)-1) ≤
        (planarFibers P s).degree (cutoff s P.card) C x) := by
  obtain ⟨r,hγr,hrs,m₁,hm₁⟩ := continuous_left_tail hγs (show 0 < η/8 by positivity) hs
  obtain ⟨N,hN,hF⟩ := extremal_subsequence s
  have hlarge : ∀ᶠ i in atTop, 4+2*M+2*m₁ ≤ N i := hN.eventually (eventually_ge_atTop _)
  have happrox : ∀ᶠ i in atTop, Theta s-η/8 ≤ F (N i) s :=
    (hF.eventually_const_lt (by linarith : Theta s-η/8 < Theta s)).mono (fun _ h => h.le)
  obtain ⟨i,hi,hcut,hpow,hinit⟩ := (hlarge.and ((hN.eventually (eventual_cutoff_loss s η hη)).and
    ((hN.eventually (eventual_power_below_cutoff hrs)).and happrox))).exists
  obtain ⟨P,hP,hPF⟩ := F_attained (N i) (by omega) s
  have hn : 4 ≤ P.card := by omega
  obtain ⟨hm0,hm,hbd⟩ := half_boundary P.card hn
  have hm1 : m₁ ≤ (P.card+1)/2 := by omega
  have hη8 := hcut.2.2
  have hpowP : (P.card : ℝ)^r ≤ cutoff s P.card := by simpa [hP] using hpow
  have hthreshold : ∀ m : ℕ, (P.card+1)/2 ≤ m → m ≤ P.card → (m : ℝ)^r ≤ cutoff s P.card := by
    intro m _ hmP
    exact (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) (by linarith)).trans hpowP
  obtain ⟨C,hC,hlo,hhi,hdeg⟩ := finite_extremal_core P s r (cutoff s P.card) (Theta s) η ((P.card+1)/2)
    (by omega) hm0 hm hη (by simpa [hP] using hcut.1) (by simpa [hP] using hcut.2.1)
    (by simpa [hP] using hη8) (by simpa [hPF] using hinit) hbd hthreshold
    (fun m hm _ => hm₁ m (hm1.trans hm))
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hCpos : (1:ℝ) ≤ C.card := by exact_mod_cast (show 1 ≤ C.card by omega)
  refine ⟨P,C,by omega,hC,?_,hlo,hhi,hdeg⟩
  exact (Real.rpow_le_rpow_of_exponent_le hCpos hγr.le).trans
    (hthreshold C.card hC.le hCn)

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma restricted_size_lt_card (P : Finset Plane) (s : ℝ) (D : Finset P)
    (e : fiberIndices P s) (hs : (planarFibers P s).source e ∈ D) :
    (planarFibers P s).size D e < D.card := by
  have hh : (planarFibers P s).targets e ∩ D ⊆ D.erase ((planarFibers P s).source e) := by
    intro y hy
    obtain ⟨hyT,hyD⟩ := Finset.mem_inter.mp hy
    refine Finset.mem_erase.mpr ⟨?_,hyD⟩
    intro he
    subst y
    exact (planarFibers P s).no_loop e hyT
  have hc := Finset.card_le_card hh
  rw [Finset.card_erase_of_mem hs] at hc
  have hp := Finset.card_pos.mpr ⟨_,hs⟩
  change (planarFibers P s).size D e ≤ D.card-1 at hc
  omega

lemma heavySubset_zero (P : Finset Plane) (s K lam : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hsmall : (D.card : ℝ) ≤ lam*K) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  rw [ite_eq_right]
  rintro ⟨⟨ha,hh⟩,hs⟩
  have hk := mul_le_mul_of_nonneg_left (le_of_lt ha.2) hlam
  have hm : ((planarFibers P s).size D e : ℝ) < D.card := by
    exact_mod_cast restricted_size_lt_card P s D e hs
  linarith

/-- A uniform extremal bound valid even for tiny subsets: their contribution
    is zero, rather than an uncontrolled diagonal error. -/
theorem heavySubset_uniform (P : Finset Plane) (s K lam r B : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (m₁ : ℕ) (hm1 : 2 ≤ m₁)
    (hT : (m₁ : ℝ) ≤ lam*K)
    (hthreshold : (D.card : ℝ)^r ≤ lam*K)
    (hext : ∀ m : ℕ, m₁ ≤ m → m ≤ P.card → F m r ≤ B) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) ≤
      B*(D.card : ℝ)*((D.card : ℝ)-1) := by
  by_cases hm : D.card < m₁
  · have hDm : (D.card : ℝ) ≤ m₁ := by exact_mod_cast hm.le
    rw [heavySubset_zero P s K lam C D hlam (hDm.trans hT)]
    by_cases hzero : D.card=0
    · simp [hzero]
    · have hh : (1:ℝ) ≤ D.card := by exact_mod_cast (show 1 ≤ D.card by omega)
      positivity
  · have hmge : m₁ ≤ D.card := by omega
    have hDn : D.card ≤ P.card := by simpa using Finset.card_le_univ D
    have hh : (2:ℝ) ≤ D.card := by exact_mod_cast hm1.trans hmge
    have hp : 0 < (D.card : ℝ)*((D.card : ℝ)-1) := by nlinarith
    have hf := fraction_le_F (planeSubset P D) r (by simpa [planeSubset_card] using hm1.trans hmge)
    rw [pairFraction,planeSubset_card,div_le_iff₀ hp] at hf
    have hc := heavySubset_count P s K lam r C D hlam hthreshold
    have he := mul_le_mul_of_nonneg_right (hext D.card hmge hDn) hp.le
    nlinarith

lemma eventual_power_below_logsquare {s r : ℝ} (hrs : r < s) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ)^r ≤ cutoff s N / Real.log N := by
  have ho := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (sub_pos.mpr hrs)).bound (show (0:ℝ)<1 by norm_num)
  have hn : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually ho,hn.eventually (Filter.eventually_gt_atTop 1)] with N hN hp
  have hlog : 0 < Real.log N := Real.log_pos hp
  have hpow : 0 ≤ (N : ℝ)^(s-r) := Real.rpow_nonneg (by linarith) _
  simp only [Real.norm_eq_abs,Real.rpow_two,one_mul,abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),abs_of_nonneg hpow] at hN
  unfold cutoff
  rw [div_div]
  apply (le_div_iff₀ (mul_pos hlog hlog)).mpr
  calc
    (N : ℝ)^r*(Real.log N*Real.log N) ≤ (N : ℝ)^r*(N : ℝ)^(s-r) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      nlinarith
    _ = (N : ℝ)^s := by rw [← Real.rpow_add (by linarith : (0:ℝ)<N)]; congr 1; ring

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology BigOperators

def heavyCount (P : Finset Plane) (s K lam : ℝ) (C D : Finset P) : ℝ :=
  ∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
    then ((planarFibers P s).size D e : ℝ) else 0

/-- Uniform subset bounds for the finite planar core. -/
structure PreparedCore (s γ c η : ℝ) (P : Finset Plane) (C : Finset P) : Prop where
  card_two : 2 ≤ C.card
  half : (P.card+1)/2 < C.card
  large_fiber : (C.card : ℝ)^γ ≤ cutoff s P.card
  lower : (Theta s-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤
    ((planarFibers P s).edgeSet (cutoff s P.card) C).card
  upper : (((planarFibers P s).edgeSet (cutoff s P.card) C).card : ℝ) ≤
    (Theta s+η/8)*(C.card : ℝ)*((C.card : ℝ)-1)
  degree : ∀ x ∈ C, 2*(Theta s-η)*((C.card : ℝ)-1) ≤
    (planarFibers P s).degree (cutoff s P.card) C x
  subset : ∀ D : Finset P,
    heavyCount P s (cutoff s P.card) (1/Real.log C.card) C D ≤
      (Theta s+η)*(D.card : ℝ)*((D.card : ℝ)-1)
  small : ∀ D : Finset P, (D.card : ℝ) ≤ (C.card : ℝ)^(1-c) →
    heavyCount P s (cutoff s P.card) (1/Real.log C.card) C D ≤
      η*(D.card : ℝ)*((D.card : ℝ)-1)

lemma choose_above_critical (hfail : ¬ MainStatement) {s c : ℝ}
    (hc : c < 1) (hsc : (1-c)*criticalExponent < s) :
    ∃ t : ℝ, criticalExponent < t ∧ (1-c)*t < s ∧ 0 < t := by
  have hp : 0 < 1-c := by linarith
  have hb : criticalExponent < s/(1-c) := (lt_div_iff₀ hp).mpr (by nlinarith)
  obtain ⟨t,ht,hst⟩ := exists_between hb
  refine ⟨t,ht,?_,(critical_pos hfail).trans ht⟩
  have hh := (lt_div_iff₀ hp).mp hst
  nlinarith

lemma log_cutoff_comparison {N n : ℕ} {s : ℝ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    cutoff s N / Real.log N ≤ (1/Real.log n)*cutoff s N := by
  have hnr : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlog := Real.log_pos hnr
  have hlogs : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) (by exact_mod_cast hnN)
  calc
    cutoff s N / Real.log N ≤ cutoff s N / Real.log n := by
      apply div_le_div_of_nonneg_left _ hlog hlogs
      exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hlog.le.trans hlogs)
    _ = (1/Real.log n)*cutoff s N := by ring

/-- Uniformity of both subset estimates is obtained before passing to any
    arithmetic model. Tiny subsets are treated exactly, with no diagonal error. -/
theorem arbitrarily_large_prepared (hfail : ¬ MainStatement) {s γ c : ℝ}
    (hγ : 0 < γ) (hγs : γ < s) (_hc : 0 < c) (hc1 : c < 1)
    (hsc : (1-c)*criticalExponent < s) (hs : ContinuousAt Theta s)
    (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M < C.card ∧ PreparedCore s γ c η P C := by
  obtain ⟨r,hγr,hrs,m₁,hm₁⟩ := continuous_left_tail hγs hη hs
  obtain ⟨t,ht,hst,ht0⟩ := choose_above_critical hfail hc1 hsc
  obtain ⟨m₂,hm₂⟩ := eventually_atTop.mp
    ((tendsto_F_of_Theta_zero (Theta_zero_above_critical hfail ht)).eventually_lt_const hη)
  let m := max 2 (max m₁ m₂)
  have hm2 : 2 ≤ m := le_max_left _ _
  have hmr : m₁ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmt : m₂ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hr0 : 0 < r := hγ.trans hγr
  have hbig : ∀ᶠ N : ℕ in atTop, (m : ℝ) ≤ (N : ℝ)^r :=
    ((tendsto_rpow_atTop hr0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (hbig.and ((eventual_power_below_logsquare hrs).and (eventual_power_below_logsquare hst)))
  obtain ⟨P,C,hC,hhalf,hpow,hlo,hhi,hdeg⟩ :=
    arbitrarily_large_core hγ hγs hs η hη (max (max M N₀) 2)
  have hn : 2 ≤ C.card := by omega
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hg : N₀ ≤ P.card := by omega
  obtain ⟨hbigP,hpr,hpt⟩ := hN₀ P.card hg
  have hcomp := log_cutoff_comparison (s:=s) hn hCn
  have hlam : 0 ≤ 1/Real.log (C.card : ℝ) := by
    have hh := Real.log_pos (show (1:ℝ)<C.card by exact_mod_cast (show 1<C.card by omega))
    positivity
  have hT : (m : ℝ) ≤ (1/Real.log (C.card : ℝ))*cutoff s P.card := hbigP.trans (hpr.trans hcomp)
  refine ⟨P,C,by omega,hn,hhalf,hpow,hlo,hhi,hdeg,?_,?_⟩
  · intro D
    have hDn : D.card ≤ P.card := by simpa using Finset.card_le_univ D
    have hDP : (D.card : ℝ)^r ≤ (P.card : ℝ)^r :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hDn) hr0.le
    exact heavySubset_uniform P s (cutoff s P.card) (1/Real.log C.card) r (Theta s+η) C D hlam
      (by linarith [Theta_nonneg s]) m hm2 hT (hDP.trans (hpr.trans hcomp))
      (fun j hj _ => hm₁ j (hmr.trans hj))
  · intro D hD
    have hDP : (D.card : ℝ)^t ≤ (P.card : ℝ)^((1-c)*t) := by
      calc
        (D.card : ℝ)^t ≤ ((C.card : ℝ)^(1-c))^t :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hD ht0.le
        _ = (C.card : ℝ)^((1-c)*t) := (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
        _ ≤ (P.card : ℝ)^((1-c)*t) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hCn) (by positivity)
    exact heavySubset_uniform P s (cutoff s P.card) (1/Real.log C.card) t η C D hlam hη.le
      m hm2 hT (hDP.trans (hpt.trans hcomp)) (fun j hj _ => (hm₂ j (hmt.trans hj)).le)

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
