import OAI.Combinatorics.ListHadwiger.Density

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def Stable (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬G.Adj v w

lemma Stable.mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {I J : Finset V} (h : Stable G I) (hJI : J ⊆ I) :
    Stable G J := fun v hv w hw => h v (hJI hv) w (hJI hw)

@[simp] lemma stable_empty {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Stable G ∅ := by simp [Stable]
@[simp] lemma stable_singleton {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) : Stable G {v} := by
  simp [Stable]

def Cover (G : SimpleGraph V) (μ : Finset V → ℝ) : Prop :=
  (∀ I, 0 ≤ μ I) ∧ (∀ I, ¬Stable G I → μ I = 0) ∧
    ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0

noncomputable def cost (μ : Finset V → ℝ) : ℝ := ∑ I, μ I

noncomputable def number (G : SimpleGraph V) : ℝ :=
  sInf {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c}

lemma cost_nonneg {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) : 0 ≤ cost μ :=
  Finset.sum_nonneg (fun I _ => h.1 I)

noncomputable def singletonWeights (I : Finset V) : ℝ :=
  ∑ v : V, if I = {v} then 1 else 0

lemma singletonWeights_cover (G : SimpleGraph V) : Cover G singletonWeights := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num
  · intro I hn
    apply Finset.sum_eq_zero
    intro v _
    rw [ite_eq_right]
    rintro rfl
    exact hn (stable_singleton G v)
  · intro v
    have hpos (I : Finset V) : 0 ≤ (if v ∈ I then singletonWeights I else 0) := by
      split_ifs
      · exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
      · exact le_rfl
    have h := Finset.single_le_sum (fun I _ => hpos I) (Finset.mem_univ ({v} : Finset V))
    have hm : singletonWeights ({v} : Finset V) = 1 := by
      simp [singletonWeights,Finset.singleton_inj]
    simpa [hm] using h

lemma singletonWeights_cost : cost (singletonWeights (V := V)) = Fintype.card V := by
  classical
  simp only [cost,singletonWeights]
  rw [Finset.sum_comm]
  simp

lemma costs_nonempty (G : SimpleGraph V) :
    ({c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} : Set ℝ).Nonempty :=
  ⟨_,singletonWeights,singletonWeights_cover G,rfl⟩

lemma costs_bddBelow (G : SimpleGraph V) :
    BddBelow {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} := by
  refine ⟨0,?_⟩
  rintro c ⟨μ,hμ,rfl⟩
  exact cost_nonneg hμ

lemma number_le_cost {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    number G ≤ cost μ := csInf_le (costs_bddBelow G) ⟨μ,h,rfl⟩

lemma number_nonneg (G : SimpleGraph V) : 0 ≤ number G :=
  le_csInf (costs_nonempty G) (by rintro c ⟨μ,hμ,rfl⟩; exact cost_nonneg hμ)

lemma number_le_card (G : SimpleGraph V) : number G ≤ Fintype.card V := by
  simpa only [singletonWeights_cost] using number_le_cost (singletonWeights_cover G)

lemma Cover.clamp {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    Cover G (fun I => min (μ I) 1) := by
  classical
  refine ⟨fun I => le_min (h.1 I) zero_le_one,?_,?_⟩
  · intro I hn
    change min (μ I) 1 = 0
    rw [h.2.1 I hn]
    norm_num
  · intro v
    by_cases hall : ∀ I, v ∈ I → μ I ≤ 1
    · have heq : (∑ I, if v ∈ I then min (μ I) 1 else 0) =
          ∑ I, if v ∈ I then μ I else 0 := by
        apply Finset.sum_congr rfl
        intro I _
        split_ifs with hv
        · rw [min_eq_left (hall I hv)]
        · rfl
      rw [heq]
      exact h.2.2 v
    · push Not at hall
      obtain ⟨I,hv,hI⟩ := hall
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Finset V)))
        (f := fun J => if v ∈ J then min (μ J) 1 else 0)
        (fun J _ => by split_ifs; exact le_min (h.1 J) zero_le_one; exact le_rfl)
        (Finset.mem_univ I)
      simpa only [ite_eq_left hv,min_eq_right (le_of_lt hI)] using hs

lemma cover_isClosed (G : SimpleGraph V) : IsClosed {μ : Finset V → ℝ | Cover G μ} := by
  change IsClosed ({μ : Finset V → ℝ | ∀ I, 0 ≤ μ I} ∩
    ({μ | ∀ I, ¬Stable G I → μ I = 0} ∩
     {μ | ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0}))
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun I => isClosed_le continuous_const (continuous_apply I)
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases h : Stable G I
    · simp only [h,not_true_eq_false,false_implies,Set.ofPred_true]
      exact isClosed_univ
    · simp only [h,not_false_eq_true,true_implies]
      exact isClosed_eq (continuous_apply I) continuous_const
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    apply continuous_finsetSum
    intro I _
    by_cases hv : v ∈ I
    · simpa only [ite_eq_left hv] using continuous_apply I
    · simp only [ite_eq_right hv]
      exact continuous_const

lemma cost_continuous {V : Type} [Fintype V] [DecidableEq V] : Continuous (cost (V := V)) := by
  apply continuous_finsetSum
  intro I _
  exact continuous_apply I

theorem optimum_exists (G : SimpleGraph V) : ∃ μ, Cover G μ ∧ cost μ = number G := by
  classical
  let K : Set ((Finset V) → ℝ) := Set.Icc 0 1 ∩ {μ | Cover G μ}
  have hcomp : IsCompact K := isCompact_Icc.inter_right (cover_isClosed G)
  have hne : K.Nonempty := by
    refine ⟨fun I => min (singletonWeights I) 1,⟨?_,?_⟩,(singletonWeights_cover G).clamp⟩
    · intro I
      exact le_min ((singletonWeights_cover G).1 I) zero_le_one
    · intro I
      exact min_le_right _ _
  obtain ⟨μ,hμ,hmin⟩ := hcomp.exists_isMinOn hne cost_continuous.continuousOn
  refine ⟨μ,hμ.2,le_antisymm ?_ (number_le_cost hμ.2)⟩
  apply le_csInf (costs_nonempty G)
  rintro c ⟨ν,hν,rfl⟩
  apply (hmin (show (fun I => min (ν I) 1) ∈ K from ?_)).trans
    (Finset.sum_le_sum (fun I _ => min_le_left (ν I) 1))
  exact ⟨⟨fun I => le_min (hν.1 I) zero_le_one,fun I => min_le_right _ _⟩,hν.clamp⟩

lemma number_le_iff (G : SimpleGraph V) (r : ℝ) :
    number G ≤ r ↔ ∃ μ, Cover G μ ∧ cost μ ≤ r := by
  constructor
  · intro h
    obtain ⟨μ,hμ,heq⟩ := optimum_exists G
    exact ⟨μ,hμ,heq ▸ h⟩
  · rintro ⟨μ,hμ,hcost⟩
    exact (number_le_cost hμ).trans hcost

def Dual (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ I, Stable G I → ∑ v ∈ I, w v ≤ 1

lemma Dual.le_one {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (v : V) : w v ≤ 1 := by
  simpa using hw.2 {v} (stable_singleton G v)

lemma dual_zero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Dual G (fun _ => 0) := by
  simp [Dual]

lemma dual_isClosed {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : IsClosed {w : V → ℝ | Dual G w} := by
  classical
  change IsClosed ({w : V → ℝ | ∀ v, 0 ≤ w v} ∩
    {w | ∀ I, Stable G I → ∑ v ∈ I, w v ≤ 1})
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases hI : Stable G I
    · simp only [hI,true_implies]
      apply isClosed_le _ continuous_const
      exact continuous_finsetSum I (fun v _ => continuous_apply v)
    · simp only [hI,false_implies,Set.ofPred_true]
      exact isClosed_univ

lemma dual_maximum (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∀ z, Dual G z → ∑ v, z v ≤ ∑ v, w v := by
  classical
  have hc : IsCompact {w : V → ℝ | Dual G w} :=
    isCompact_Icc.of_isClosed_subset (dual_isClosed G) (by
      intro w hw
      exact ⟨hw.1,hw.le_one⟩)
  exact hc.exists_isMaxOn ⟨_,dual_zero G⟩
    (continuous_finsetSum Finset.univ (fun v _ => continuous_apply v)).continuousOn

lemma weak_duality {G : SimpleGraph V} {μ : Finset V → ℝ} {w : V → ℝ}
    (hμ : Cover G μ) (hw : Dual G w) : ∑ v, w v ≤ cost μ := by
  classical
  calc
    ∑ v, w v ≤ ∑ v, w v * ∑ I, if v ∈ I then μ I else 0 := by
      apply Finset.sum_le_sum
      intro v _
      simpa using mul_le_mul_of_nonneg_left (hμ.2.2 v) (hw.1 v)
    _ = ∑ I, μ I * ∑ v ∈ I, w v := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      simp only [mul_ite,mul_zero,mul_comm (w _) (μ I),← Finset.mul_sum]
      simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [Finset.mul_sum]
    _ ≤ cost μ := by
      apply Finset.sum_le_sum
      intro I _
      by_cases hI : Stable G I
      · simpa using mul_le_mul_of_nonneg_left (hw.2 I hI) (hμ.1 I)
      · simp [hμ.2.1 I hI]

lemma dual_le_number {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) :
    ∑ v, w v ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  rw [← heq]
  exact weak_duality hμ hw

noncomputable def indicator (I : Finset V) : V → ℝ := fun v => if v ∈ I then 1 else 0

lemma indicator_empty {V : Type} [Fintype V] [DecidableEq V] : indicator (∅ : Finset V) = 0 := by ext v; simp [indicator]

lemma constant_mem_hull_cover (G : SimpleGraph V) {r : ℝ} (hr : 0 < r)
    (hx : (fun _ : V => 1 / r) ∈ convexHull ℝ {x | ∃ I, Stable G I ∧ indicator I = x}) :
    ∃ μ, Cover G μ ∧ cost μ = r := by
  classical
  obtain ⟨ι,hi,w,z,hw,hws,hz,hx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose I hI heq using hz
  let μ : Finset V → ℝ := fun J => ∑ i, if I i = J then r * w i else 0
  have hmass : cost μ = r := by
    unfold cost μ
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum,hws,mul_one]
  refine ⟨μ,⟨?_,?_,?_⟩,hmass⟩
  · intro J
    exact Finset.sum_nonneg fun i _ => by split_ifs; exact mul_nonneg hr.le (hw i); exact le_rfl
  · intro J hn
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro he
    exact hn (he ▸ hI i)
  · intro v
    have hxv := congrFun hx v
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hxv
    have hzv (i : ι) : z i v = if v ∈ I i then 1 else 0 := congrFun (heq i).symm v
    simp only [hzv,mul_ite,mul_one,mul_zero] at hxv
    have hm : (∑ J, if v ∈ J then μ J else 0) = r * ∑ i, if v ∈ I i then w i else 0 := by
      have hdis (J : Finset V) : (if v ∈ J then μ J else 0) =
          ∑ i, if v ∈ J then (if I i = J then r * w i else 0) else 0 := by
        by_cases h : v ∈ J <;> simp [h,μ]
      simp only [hdis]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have heq : (fun J : Finset V => if v ∈ J then if I i = J then r * w i else 0 else 0) =
          (fun J => if I i = J then (if v ∈ I i then r * w i else 0) else 0) := by
        funext J
        by_cases hh : I i = J
        · subst J; simp
        · simp [hh]
      rw [heq]
      simp [mul_ite]
    rw [hm,hxv]
    exact le_of_eq (by field_simp)

lemma functional_eq_sum (f : StrongDual ℝ (V → ℝ)) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have hx : x = ∑ v, x v • Pi.single v 1 := by
    ext u
    simp [Pi.single_apply,smul_eq_mul,Finset.sum_apply]
  conv_lhs => rw [hx]
  simp

lemma functional_indicator (f : StrongDual ℝ (V → ℝ)) (I : Finset V) :
    f (indicator I) = ∑ v ∈ I, f (Pi.single v 1) := by
  classical
  rw [functional_eq_sum]
  simp only [indicator,ite_mul,one_mul,zero_mul,← Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma dual_above (G : SimpleGraph V) {r : ℝ} (hr : 0 < r) (hrn : r < number G) :
    ∃ w, Dual G w ∧ r < ∑ v, w v := by
  classical
  let S : Set (V → ℝ) := {x | ∃ I, Stable G I ∧ indicator I = x}
  have hfin : S.Finite := (Set.finite_range (indicator (V := V))).subset (by
    rintro x ⟨I,hI,rfl⟩; exact ⟨I,rfl⟩)
  have hn : (fun _ : V => 1/r) ∉ convexHull ℝ S := by
    intro hx
    obtain ⟨μ,hμ,hm⟩ := constant_mem_hull_cover G hr hx
    have hh := number_le_cost hμ
    linarith
  obtain ⟨f,u,hf,hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ S) (hfin.isClosed_convexHull ℝ) hn
  have hi (I : Finset V) (hI : Stable G I) :
      ∑ v ∈ I, f (Pi.single v 1) < u := by
    rw [← functional_indicator]
    exact hf _ (subset_convexHull ℝ S ⟨I,hI,rfl⟩)
  have hup : 0 < u := by simpa using hi ∅ (stable_empty G)
  let a : V → ℝ := fun v => f (Pi.single v 1)
  let w : V → ℝ := fun v => max (a v) 0 / u
  refine ⟨w,⟨fun v => div_nonneg (le_max_right _ _) hup.le,?_⟩,?_⟩
  · intro I hI
    have hm : (∑ v ∈ I, max (a v) 0) = ∑ v ∈ I.filter (fun v => 0 ≤ a v), a v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : 0 ≤ a v
      · simp [hv]
      · simp [hv,max_eq_right (le_of_not_ge hv)]
    have hb := hi (I.filter (fun v => 0 ≤ a v))
      (hI.mono (Finset.filter_subset _ _))
    change ∑ v ∈ I, max (a v) 0 / u ≤ 1
    rw [← Finset.sum_div,div_le_one hup]
    rw [hm]
    exact hb.le
  · have hconst : f (fun _ : V => 1/r) = (∑ v, a v) / r := by
      rw [functional_eq_sum]
      simp only [← Finset.mul_sum,div_eq_mul_inv,mul_comm,mul_one,a]
    rw [hconst] at hu
    have hbig : r * u < ∑ v, a v := by
      have := (lt_div_iff₀ hr).mp hu
      nlinarith
    have hle : (∑ v, a v) ≤ ∑ v, max (a v) 0 :=
      Finset.sum_le_sum (fun v _ => le_max_left _ _)
    change r < ∑ v, max (a v) 0 / u
    rw [← Finset.sum_div,lt_div_iff₀ hup]
    exact hbig.trans_le hle

theorem duality (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∑ v, w v = number G := by
  classical
  obtain ⟨w,hw,hm⟩ := dual_maximum G
  refine ⟨w,hw,le_antisymm (dual_le_number hw) ?_⟩
  by_contra hh
  have hh' : (∑ v, w v) < number G := lt_of_not_ge hh
  have hn : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => hw.1 v)
  let r := ((∑ v, w v) + number G) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrn : r < number G := by dsimp [r]; linarith
  obtain ⟨z,hz,hrz⟩ := dual_above G hr hrn
  have hzw := hm z hz
  dsimp [r] at hrz
  linarith

noncomputable def transport {α β : Type} [Fintype α] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (b : β) : ℝ := ∑ a, if f a = b then μ a else 0

lemma transport_expect {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (X : β → ℝ) :
    (∑ b, transport μ f b * X b) = ∑ a, μ a * X (f a) := by
  classical
  simp only [transport,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul]
  simp

lemma transport_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) : ∑ b, transport μ f b = ∑ a, μ a := by
  simpa only [mul_one] using transport_expect μ f (fun _ => 1)

lemma transport_nonneg {α β : Type} [Fintype α] [DecidableEq β]
    {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f : α → β) (b : β) : 0 ≤ transport μ f b := by
  exact Finset.sum_nonneg fun a _ => by split_ifs; exact hμ a; exact le_rfl

noncomputable def marginal (μ : Finset V → ℝ) (v : V) : ℝ :=
  ∑ I, if v ∈ I then μ I else 0

lemma marginal_eq_expect (μ : Finset V → ℝ) (v : V) :
    marginal μ v = ∑ I, μ I * indicator I v := by
  classical
  simp [marginal,indicator,mul_ite]

noncomputable def prune (μ : Finset V → ℝ) (v : V) (p : ℝ) : Finset V → ℝ :=
  fun I => p * μ I + (1-p) * transport μ (fun J => J.erase v) I

lemma prune_cost (μ : Finset V → ℝ) (v : V) (p : ℝ) : cost (prune μ v p) = cost μ := by
  classical
  simp only [cost,prune,Finset.sum_add_distrib,← Finset.mul_sum,transport_sum]
  ring

lemma prune_marginal (μ : Finset V → ℝ) (v u : V) (p : ℝ) :
    marginal (prune μ v p) u = if u = v then p * marginal μ u else marginal μ u := by
  classical
  rw [marginal_eq_expect]
  simp only [prune,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,
    transport_expect]
  rw [← marginal_eq_expect]
  by_cases huv : u = v
  · subst u
    simp [indicator]
  · have hInd (J : Finset V) : indicator (J.erase v) u = indicator J u := by
      simp [indicator,Finset.mem_erase,huv]
    simp only [hInd,← marginal_eq_expect,huv,ite_false]
    ring

lemma prune_cover {G : SimpleGraph V} {μ : Finset V → ℝ} (hμ : Cover G μ)
    (v : V) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ p * marginal μ v) : Cover G (prune μ v p) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact add_nonneg (mul_nonneg hp (hμ.1 I))
      (mul_nonneg (sub_nonneg.mpr hp1) (transport_nonneg hμ.1 _ I))
  · intro I hn
    have hz : transport μ (fun J => J.erase v) I = 0 := by
      apply Finset.sum_eq_zero
      intro J _
      split_ifs with hh
      · apply hμ.2.1 J
        intro hJ
        apply hn
        rw [← hh]
        exact hJ.mono (Finset.erase_subset _ _)
      · rfl
    simp [prune,hμ.2.1 I hn,hz]
  · intro u
    change 1 ≤ marginal (prune μ v p) u
    rw [prune_marginal]
    split_ifs with hu
    · simpa only [hu] using hm
    · exact hμ.2.2 u

lemma exact_cover (G : SimpleGraph V) {μ : Finset V → ℝ} (hμ : Cover G μ) :
    ∃ ν, Cover G ν ∧ cost ν = cost μ ∧ ∀ v, marginal ν v = 1 := by
  classical
  have step (s : Finset V) : ∃ ν, Cover G ν ∧ cost ν = cost μ ∧
      (∀ v ∈ s, marginal ν v = 1) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨μ,hμ,rfl,by simp⟩
    | @insert v s hvs ih =>
      obtain ⟨ν,hν,hcost,hex⟩ := ih
      let p := 1 / marginal ν v
      have hv : 1 ≤ marginal ν v := hν.2.2 v
      have hvp : 0 < marginal ν v := lt_of_lt_of_le zero_lt_one hv
      have hpp : 0 ≤ p := div_nonneg zero_le_one hvp.le
      have hp1 : p ≤ 1 := (div_le_one hvp).mpr hv
      have he : p * marginal ν v = 1 := by dsimp [p]; field_simp
      refine ⟨prune ν v p,prune_cover hν v hpp hp1 he.ge,?_,?_⟩
      · rw [prune_cost,hcost]
      · intro u hu
        rw [Finset.mem_insert] at hu
        rw [prune_marginal]
        rcases hu with rfl | hu
        · simpa using he
        · have huv : u ≠ v := by rintro rfl; exact hvs hu
          rw [ite_eq_right huv]
          exact hex u hu
  obtain ⟨ν,hν,hcost,hex⟩ := step Finset.univ
  exact ⟨ν,hν,hcost,fun v => hex v (Finset.mem_univ v)⟩

lemma marginal_sum (μ : Finset V → ℝ) :
    (∑ v, marginal μ v) = ∑ I, μ I * I.card := by
  classical
  simp only [marginal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp [mul_comm]

lemma partition_small {V : Type} [Fintype V] [DecidableEq V] (I : Finset V) {M : ℕ} (hM : 1 ≤ M) :
    ∃ P : Finset (Finset V),
      (∀ J ∈ P, J ⊆ I ∧ J.Nonempty ∧ J.card ≤ M) ∧
      (∀ v, (∑ J ∈ P, if v ∈ J then (1 : ℝ) else 0) = if v ∈ I then 1 else 0) ∧
      M * P.card < I.card + M := by
  classical
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I = ∅
  · subst I
    exact ⟨∅,by simp,by simp,by simp; omega⟩
  by_cases hsmall : I.card ≤ M
  · refine ⟨{I},?_,?_,?_⟩
    · intro J hJ
      have : J = I := Finset.mem_singleton.mp hJ
      subst J
      exact ⟨Finset.Subset.refl _,Finset.nonempty_iff_ne_empty.mpr hI,hsmall⟩
    · intro v
      rw [Finset.sum_singleton]
    · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
      simp only [Finset.card_singleton,mul_one]
      omega
  have hlt : M < I.card := lt_of_not_ge hsmall
  obtain ⟨J,hJI,hJcard⟩ := Finset.exists_subset_card_eq hlt.le
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hdiff : (I \ J).card + M = I.card := by
    simpa [hJcard] using Finset.card_sdiff_add_card_eq_card hJI
  have hss : I \ J ⊂ I := by
    exact (Finset.ssubset_iff_subset_ne).mpr ⟨Finset.sdiff_subset,by
      intro he
      have hh := congrArg Finset.card he
      omega⟩
  obtain ⟨P,hP,hcover,hcard⟩ := ih (I \ J) hss
  have hJP : J ∉ P := by
    intro h
    obtain ⟨v,hv⟩ := hJne
    have hh := (hP J h).1 hv
    exact (Finset.mem_sdiff.mp hh).2 hv
  refine ⟨insert J P,?_,?_,?_⟩
  · intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact ⟨hJI,hJne,hJcard.le⟩
    · exact ⟨(hP K hK).1.trans Finset.sdiff_subset,(hP K hK).2⟩
  · intro v
    rw [Finset.sum_insert hJP,hcover]
    by_cases hvJ : v ∈ J
    · have hvI := hJI hvJ
      simp [hvJ,hvI]
    · by_cases hvI : v ∈ I <;> simp [hvJ,hvI]
  · rw [Finset.card_insert_of_notMem hJP,mul_add,mul_one]
    omega

lemma partition_small_real (I : Finset V) {M : ℕ} (hM : 1 ≤ M) :
    ∃ P : Finset (Finset V),
      (∀ J ∈ P, J ⊆ I ∧ J.Nonempty ∧ J.card ≤ M) ∧
      (∀ v, (∑ J ∈ P, if v ∈ J then (1 : ℝ) else 0) = if v ∈ I then 1 else 0) ∧
      (P.card : ℝ) ≤ 1 + I.card / M := by
  obtain ⟨P,hP,hv,hc⟩ := partition_small I hM
  refine ⟨P,hP,hv,?_⟩
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hh : (M : ℝ) * P.card ≤ (I.card : ℝ) + M := by exact_mod_cast hc.le
  have he : (1 + (I.card : ℝ) / M) * M = I.card + M := by field_simp; ring
  nlinarith

noncomputable def splitWeights (μ : Finset V → ℝ)
    (P : Finset V → Finset (Finset V)) (J : Finset V) : ℝ :=
  ∑ I, if J ∈ P I then μ I else 0

lemma splitWeights_sum (μ : Finset V → ℝ) (P : Finset V → Finset (Finset V)) :
    cost (splitWeights μ P) = ∑ I, μ I * (P I).card := by
  classical
  unfold cost splitWeights
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp [mul_comm]

lemma splitWeights_marginal (μ : Finset V → ℝ) (P : Finset V → Finset (Finset V))
    (hP : ∀ I v, (∑ J ∈ P I, if v ∈ J then (1:ℝ) else 0) = if v ∈ I then 1 else 0)
    (v : V) : marginal (splitWeights μ P) v = marginal μ v := by
  classical
  rw [marginal_eq_expect]
  simp only [splitWeights,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  have he : (∑ J, (if J ∈ P I then μ I else 0) * indicator J v) =
      μ I * ∑ J ∈ P I, if v ∈ J then (1 : ℝ) else 0 := by
    simp only [ite_mul,zero_mul]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    rw [Finset.mul_sum]
    rfl
  rw [he,hP I v]
  simp only [mul_ite,mul_one,mul_zero]

lemma bounded_cover (G : SimpleGraph V) {r : ℝ} (hf : number G ≤ r)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ ν : Finset V → ℝ,
      (∀ J, 0 ≤ ν J) ∧
      (∀ J, ν J ≠ 0 → Stable G J ∧ J.card ≤ M) ∧
      (∀ v, marginal ν v = 1) ∧ cost ν ≤ r + Fintype.card V / M := by
  classical
  obtain ⟨μ,hμ,hm⟩ := (number_le_iff G r).mp hf
  obtain ⟨μ',hμ',hcost,hexact⟩ := exact_cover G hμ
  have hc : cost μ' ≤ r := hcost ▸ hm
  choose P hP hvertex hpbound using fun I : Finset V => partition_small_real I hM
  let ν := splitWeights μ' P
  have hpos (J : Finset V) : 0 ≤ ν J :=
    Finset.sum_nonneg (fun I _ => by split_ifs; exact hμ'.1 I; exact le_rfl)
  refine ⟨ν,hpos,?_,?_,?_⟩
  · intro J hJ
    by_contra hbad
    apply hJ
    apply Finset.sum_eq_zero
    intro I _
    split_ifs with hh
    · apply hμ'.2.1 I
      intro hI
      exact hbad ⟨hI.mono (hP I J hh).1,(hP I J hh).2.2⟩
    · rfl
  · intro v
    rw [splitWeights_marginal μ' P hvertex]
    exact hexact v
  · rw [splitWeights_sum]
    calc
      ∑ I, μ' I * (P I).card ≤ ∑ I, μ' I * (1 + I.card / M) := by
        exact Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left (hpbound I) (hμ'.1 I))
      _ = cost μ' + (∑ I, μ' I * I.card) / M := by
        simp only [mul_add,mul_one,mul_div_assoc,Finset.sum_add_distrib,Finset.sum_div,cost]
      _ = cost μ' + Fintype.card V / M := by
        rw [← marginal_sum]
        simp only [hexact,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      _ ≤ r + Fintype.card V / M := by linarith

theorem bounded_sampling (G : SimpleGraph V) {n r : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (horder : (Fintype.card V : ℝ) ≤ n)
    (hf : number G ≤ r) :
    ∃ π : Finset V → ℝ,
      (∀ I, 0 ≤ π I) ∧ (∑ I, π I = 1) ∧
      (∀ I, π I ≠ 0 → Stable G I ∧ I.card ≤ ⌈n/r⌉₊) ∧
      ∀ v, marginal π v = 1 / (2*r) := by
  classical
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hd : 0 < 2*r := by positivity
  let M : ℕ := ⌈n/r⌉₊
  have hM : 1 ≤ M := Nat.ceil_pos.mpr (div_pos (lt_of_lt_of_le zero_lt_one hn) hrp)
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hnr : n / r ≤ (M : ℝ) := Nat.le_ceil _
  have hquot : (Fintype.card V : ℝ) / M ≤ r := by
    apply (div_le_iff₀ hMp).mpr
    have hh := (div_le_iff₀ hrp).mp hnr
    nlinarith
  obtain ⟨ν,hν,hstab,hv,hcost⟩ := bounded_cover G hf hM
  have hmass : cost ν ≤ 2*r := by linarith
  let π : Finset V → ℝ := fun I =>
    (ν I + if I = ∅ then 2*r - cost ν else 0) / (2*r)
  refine ⟨π,?_,?_,?_,?_⟩
  · intro I
    exact div_nonneg (add_nonneg (hν I) (by split_ifs; linarith; exact le_rfl)) hd.le
  · dsimp [π]
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change (cost ν + (2*r - cost ν)) / (2*r) = 1
    field_simp
    ring
  · intro I hI
    by_cases he : I = ∅
    · subst I
      exact ⟨stable_empty G,by simp⟩
    · exact hstab I (by intro hh; apply hI; simp [π,he,hh])
  · intro v
    have he (I : Finset V) : (if v ∈ I then π I else 0) =
        (if v ∈ I then ν I else 0) / (2*r) := by
      by_cases hvI : v ∈ I
      · have hi : I ≠ ∅ := by rintro rfl; simp at hvI
        simp [π,hvI,hi]
      · simp [hvI]
    simp only [marginal,he,← Finset.sum_div]
    change marginal ν v / (2*r) = 1 / (2*r)
    rw [hv]

lemma cover_comap {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {μ : Finset V → ℝ} (hμ : Cover G μ) (f : W → V) :
    ∃ ν, Cover (G.comap f) ν ∧ cost ν = cost μ := by
  classical
  let pull : Finset V → Finset W := fun I => Finset.univ.filter (fun w => f w ∈ I)
  let ν := transport μ pull
  have hstable (I : Finset V) (hI : Stable G I) : Stable (G.comap f) (pull I) := by
    intro u hu v hv hadj
    exact hI (f u) (Finset.mem_filter.mp hu).2 (f v) (Finset.mem_filter.mp hv).2 hadj
  refine ⟨ν,⟨transport_nonneg hμ.1 pull,?_,?_⟩,transport_sum μ pull⟩
  · intro J hn
    apply Finset.sum_eq_zero
    intro I _
    split_ifs with he
    · apply hμ.2.1 I
      intro hI
      apply hn
      rw [← he]
      exact hstable I hI
    · rfl
  · intro w
    change 1 ≤ marginal ν w
    rw [marginal_eq_expect,transport_expect]
    have he (I : Finset V) : indicator (pull I) w = indicator I (f w) := by
      simp [indicator,pull]
    simp only [he,← marginal_eq_expect]
    exact hμ.2.2 (f w)

lemma number_comap {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (f : W → V) : number (G.comap f) ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  obtain ⟨ν,hν,hcost⟩ := cover_comap hμ f
  exact (number_le_cost hν).trans_eq (hcost.trans heq)

lemma number_induce (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)] :
    number (G.induce S) ≤ number G := number_comap G Subtype.val

lemma Dual.comap {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (f : W → V)
    (hf : Function.Injective f) : Dual (G.comap f) (fun v => w (f v)) := by
  classical
  refine ⟨fun v => hw.1 (f v),?_⟩
  intro I hI
  have hstable : Stable G (I.image f) := by
    intro u hu v hv hadj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact hI a ha b hb hadj
  have hh := hw.2 (I.image f) hstable
  simpa only [Finset.sum_image (fun _ _ _ _ h => hf h)] using hh

lemma number_le_induce_add (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)] :
    number G ≤ number (G.induce S) + Fintype.card ↥(Sᶜ) := by
  classical
  obtain ⟨w,hw,heq⟩ := duality G
  have hrestr : (∑ v : S, w v) ≤ number (G.induce S) :=
    dual_le_number (hw.comap Subtype.val Subtype.val_injective)
  have hout : (∑ v : ↥(Sᶜ), w v) ≤ Fintype.card ↥(Sᶜ) := by
    calc
      _ ≤ ∑ _ : ↥(Sᶜ), (1 : ℝ) := Finset.sum_le_sum (fun v _ => hw.le_one v)
      _ = _ := by simp
  have hsplit : (∑ v, w v) = (∑ v : S, w v) + ∑ v : ↥(Sᶜ), w v := by
    exact (Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ S) w).symm
  rw [← heq,hsplit]
  linarith

end LinearListHadwiger.Fractional

end OAI
