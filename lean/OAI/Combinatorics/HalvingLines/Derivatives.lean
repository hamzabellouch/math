import OAI.Combinatorics.HalvingLines.MeasureBounds

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma inv_cube_rpow {q : ℝ} (hq : 0 < q) : (1/q^3)^(-(4:ℝ)/3)=q^4 := by
  have he : 1/q^3=q^(-(3:ℝ)) := by rw [Real.rpow_neg hq.le]; norm_num [one_div]
  rw [he,← Real.rpow_mul hq.le]
  norm_num

noncomputable def goodPartition (L : Data) (K : Window) (m : ℕ) : Finset Window :=
  (localPartition K (5*m)).filter (fun J => ((L.vertices J).mass : ℝ) ≤ 1/((2:ℝ)^m)^3)

lemma goodPartition_subset (L : Data) (K : Window) (m : ℕ) :
    goodPartition L K m ⊆ localPartition K (5*m) := Finset.filter_subset _ _

lemma goodPartition_disjoint (L : Data) (K : Window) (m : ℕ) :
    ∀ J∈goodPartition L K m, ∀ H∈goodPartition L K m, J≠H → Disjoint (carrier J) (carrier H) := by
  intro J hJ H hH hJH
  exact localPartition_disjoint K (5*m) (goodPartition_subset L K m hJ) (goodPartition_subset L K m hH) hJH

lemma pow_depth (K m : ℕ) : (2:ℝ)^(K+5*m)=(2:ℝ)^K*((2:ℝ)^m)^5 := by
  rw [pow_add,Nat.mul_comm 5 m,pow_mul]

lemma Converges.goodPartition_loss {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (K : Window) (m : ℕ) {A : Set Labels} (hA : MeasurableSet A) :
    (L.edgeWindow K A : ℝ)-10000/(2:ℝ)^m ≤ ∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ) := by
  classical
  let W := localPartition K (5*m)
  let u : ℝ := 1/((2:ℝ)^m)^3
  let B := W.filter (fun J => ¬ ((L.vertices J).mass : ℝ) ≤ u)
  have hu : 0 < u := by dsimp [u]; positivity
  have hcard : (B.card : ℝ) ≤ 10000*((2:ℝ)^m)^4 := by
    have hb : B ⊆ (timePartition (K.1+5*m)).filter (fun J => u < ((L.vertices J).mass : ℝ)) := by
      intro J hJ
      obtain ⟨hJ,hb⟩ := Finset.mem_filter.mp hJ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hJ).1,lt_of_not_ge hb⟩
    have ht := h.activity_tail E (K.1+5*m) hu
    rw [← filter_timePartition (K.1+5*m) (fun J => u < ((L.vertices J).mass : ℝ))] at ht
    have hi := (Nat.cast_le.mpr (Finset.card_le_card hb) : (B.card : ℝ) ≤ _)
    exact hi.trans (by simpa only [u,inv_cube_rpow (by positivity : (0:ℝ) < (2:ℝ)^m)] using ht)
  have hmass (J : Window) (hJ : J∈B) : (L.edgeWindow J A : ℝ) ≤ 1/((2:ℝ)^m)^5 := by
    have hd : J.1=K.1+5*m := mem_timePartition.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
    have hh := NNReal.coe_le_coe.mpr ((L.edgeWindow J).apply_le_mass A)
    rw [h.edgeWindow_mass hR,Nat.cast_pow,Nat.cast_ofNat,hd,pow_depth] at hh
    have he : (1:ℝ) ≤ (2:ℝ)^K.1 := one_le_pow₀ (by norm_num)
    have hp : ((2:ℝ)^m)^5 ≤ (2:ℝ)^K.1*((2:ℝ)^m)^5 :=
      le_mul_of_one_le_left (by positivity) he
    exact hh.trans (by simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < ((2:ℝ)^m)^5) hp)
  have hloss : ∑ J∈B, (L.edgeWindow J A : ℝ) ≤ 10000/(2:ℝ)^m := by
    apply (Finset.sum_le_sum hmass).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcard (by positivity)).trans
    have hn : ((2:ℝ)^m)≠0 := by positivity
    exact le_of_eq (by field_simp)
  have he : (∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ))+
      (∑ J∈B, (L.edgeWindow J A : ℝ))=(L.edgeWindow K A : ℝ) := by
    rw [← h.localPartition_sum hR K (5*m) hA]
    exact Finset.sum_filter_add_sum_filter_not W _ _
  linarith

lemma Data.goodPartition_diagonal (L : Data) (K : Window) (m : ℕ) :
    ∑ J∈goodPartition L K m, 2*((L.vertices J).mass : ℝ)^2 ≤ 2*(2:ℝ)^K.1/(2:ℝ)^m := by
  classical
  let W := goodPartition L K m
  have hs : W ⊆ timePartition (K.1+5*m) := fun J hJ =>
    (Finset.mem_filter.mp (goodPartition_subset L K m hJ)).1
  have hc : (W.card : ℝ) ≤ (2:ℝ)^(K.1+5*m) := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (timePartition_card _)
  have hsum : ∑ J∈W, 2*((L.vertices J).mass : ℝ)^2 ≤ (W.card : ℝ)*(2*(1/((2:ℝ)^m)^3)^2) := by
    have hh := Finset.sum_le_sum (s:=W) (fun J hJ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (Finset.mem_filter.mp hJ).2 2) (by norm_num : (0:ℝ)≤2))
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
  rw [pow_depth]
  have hn : ((2:ℝ)^m)≠0 := by positivity
  exact le_of_eq (by field_simp)

lemma Data.goodPartition_crossings (L : Data) (K : Window) (m : ℕ) {A : Set Labels}
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) :
    (∑ J∈goodPartition L K m, ∑ H∈goodPartition L K m,
      if J=H then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J H A : ℝ)) ≤
      2*(2:ℝ)^K.1/(2:ℝ)^m := by
  classical
  apply le_trans _ (L.goodPartition_diagonal K m)
  apply Finset.sum_le_sum
  intro J hJ
  have he : (∑ H∈goodPartition L K m,
      if J=H then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J H A : ℝ))=
      2*((L.vertices J).mass : ℝ)^2 := by
    rw [Finset.sum_eq_single J]
    · simp
    · intro H hH hHJ
      rw [ite_eq_right (Ne.symm hHJ),hnull J H
        (Finset.mem_filter.mp (goodPartition_subset L K m hJ)).2
        (Finset.mem_filter.mp (goodPartition_subset L K m hH)).2
        (goodPartition_disjoint L K m J hJ H hH (Ne.symm hHJ))]
      rfl
    · exact fun hn => (hn hJ).elim
  exact he.le

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Converges.edge_crossing_null_closed {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) {A : Set Labels} (hA : IsClosed A)
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) : L.edgeWindow K A=0 := by
  have ht : Tendsto (fun m : ℕ => ((2:ℝ)^m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlo : Tendsto (fun m : ℕ => 10000/(2:ℝ)^m) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.const_mul (10000:ℝ)
  have hup : Tendsto (fun m : ℕ => 2*(2:ℝ)^K.1/(2:ℝ)^m) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.const_mul (2*(2:ℝ)^K.1)
  have hcub : (L.edgeWindow K A : ℝ)^3 ≤ C*0 := by
    apply Limits.cubic_of_eventual_bounds (x:=fun m => ∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ))
      (b:=fun m => 2*(2:ℝ)^K.1/(2:ℝ)^m) (e:=fun _ => 0) (by positivity) hC
    · intro m; positivity
    · intro m
      simpa only [add_zero] using
        (h.partition_cubic_closed hC hcoeff herror hshort _ (goodPartition_disjoint L K m) hA).trans
          (mul_le_mul_of_nonneg_left (L.goodPartition_crossings K m hnull) hC)
    · intro ε hε
      filter_upwards [(tendsto_order.mp hlo).2 ε hε] with m hm
      have hh := h.goodPartition_loss E hR K m hA.measurableSet
      linarith
    · intro ε hε
      exact ((tendsto_order.mp hup).2 ε hε).mono (fun _ hh => by simpa only [zero_add] using hh.le)
    · exact tendsto_const_nhds
  apply NNReal.coe_injective
  change (L.edgeWindow K A : ℝ)=0
  have hp : 0 ≤ (L.edgeWindow K A : ℝ) := by positivity
  have he : (L.edgeWindow K A : ℝ)^3=0 :=
    le_antisymm (by simpa only [mul_zero] using hcub) (pow_nonneg hp _)
  exact (pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp he

lemma Converges.edge_crossing_null {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) {A : Set Labels} (hA : MeasurableSet A)
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) : L.edgeWindow K A=0 := by
  by_contra hn
  have hp : 0 < (L.edgeWindow K : Measure Labels) A := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hn)
  obtain ⟨T,hTA,hT,hpos⟩ := hA.exists_lt_isCompact hp
  have hz := h.edge_crossing_null_closed E hR hC hcoeff herror hshort K hT.isClosed
    (fun J H hJ hH hd => le_antisymm (((L.crossings J H).apply_mono hTA).trans_eq (hnull J H hJ hH hd)) (by positivity))
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz,ENNReal.coe_zero] at hpos
  exact lt_irrefl _ hpos

def CrossingPairs (K : Window) := {JH : Window×Window //
  carrier JH.1⊆carrier K ∧ carrier JH.2⊆carrier K ∧ Disjoint (carrier JH.1) (carrier JH.2)}

instance crossingPairsCountable (K : Window) : Countable (CrossingPairs K) := by
  unfold CrossingPairs
  infer_instance

lemma Converges.edge_crossing_ac {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) : (L.edgeWindow K : Measure Labels) ≪
      Measure.sum (fun JH : CrossingPairs K => (L.crossings JH.val.1 JH.val.2 : Measure Labels)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hn
  have hz (J H : Window) (hJ : carrier J⊆carrier K) (hH : carrier H⊆carrier K)
      (hd : Disjoint (carrier J) (carrier H)) : L.crossings J H A=0 := by
    have hh := Measure.sum_apply_eq_zero.mp hn (⟨(J,H),hJ,hH,hd⟩ : CrossingPairs K)
    simpa only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,ENNReal.coe_eq_zero] using hh
  have hh := h.edge_crossing_null E hR hC hcoeff herror hshort K hA hz
  simpa only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,ENNReal.coe_eq_zero] using hh

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimit
open Filter Set MeasureTheory Metric
open scoped Topology unitInterval

noncomputable def extendRank {X : Type*} (p : X → Point) (c : X → I) (x : Point) : I :=
  ⨆ a : X, if p a ≤ x then c a else ⊥

lemma extendRank_monotone {X : Type*} (p : X → Point) (c : X → I) :
    Monotone (extendRank p c) := by
  intro x y hxy
  apply iSup_le
  intro a
  by_cases ha : p a ≤ x
  · simpa only [extendRank, ite_eq_left ha, ite_eq_left (ha.trans hxy)] using
      (le_iSup (fun b : X => if p b ≤ y then c b else ⊥) a)
  · simp only [ite_eq_right ha, bot_le]

lemma extendRank_eq {X : Type*} (p : X → Point) (c : X → I)
    (hc : ∀ a b, p a ≤ p b → c a ≤ c b) (a : X) : extendRank p c (p a) = c a := by
  apply le_antisymm
  · apply iSup_le
    intro b
    split_ifs with hb
    · exact hc b a hb
    · exact bot_le
  · simpa only [extendRank, ite_eq_left le_rfl] using
      (le_iSup (fun b : X => if p b ≤ p a then c b else ⊥) a)

theorem joint_tendsto_of_grid {f : ℕ → Point → I}
    (hf : ∀ n, Monotone (f n)) {g : RatPoint → I}
    (hg : ∀ q, Tendsto (fun n => f n (ratPoint q)) atTop (𝓝 (g q)))
    {x : Point} (hc : ContinuousAt (lowerGrid g) x) :
    Tendsto (fun q : ℕ × Point => f q.1 q.2) (atTop ×ˢ 𝓝 x) (𝓝 (lowerGrid g x)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ha
    by_cases hqx : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2
    · simp only [ite_eq_left hqx] at hq
      filter_upwards [(tendsto_order.mp ((hg q).comp tendsto_fst)).1 a hq,
        (tendsto_order.mp ((continuous_fst.tendsto x).comp tendsto_snd)).1 _ hqx.1,
        (tendsto_order.mp ((continuous_snd.tendsto x).comp tendsto_snd)).1 _ hqx.2]
        with n hn hn₁ hn₂
      exact hn.trans_le (hf n.1 ⟨hn₁.le, hn₂.le⟩)
    · simp only [ite_eq_right hqx, not_lt_bot] at hq
  · intro a ha
    have hn := hc.preimage_mem_nhds (isOpen_Iio.mem_nhds ha)
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hn
    let b : Point := x + (δ / 2, δ / 2)
    have hb : b ∈ ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [b, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ), max_self]
      linarith only [hδ]
    have hba : lowerGrid g b < a := hδU hb
    obtain ⟨r₁, hxr₁, hr₁b⟩ := exists_rat_btwn
      (show x.1 < b.1 by dsimp [b]; linarith only [hδ])
    obtain ⟨r₂, hxr₂, hr₂b⟩ := exists_rat_btwn
      (show x.2 < b.2 by dsimp [b]; linarith only [hδ])
    let r : RatPoint := (r₁, r₂)
    have hra : g r < a := (grid_le_lowerGrid ⟨hr₁b, hr₂b⟩).trans_lt hba
    filter_upwards [(tendsto_order.mp ((hg r).comp tendsto_fst)).2 a hra,
      (tendsto_order.mp ((continuous_fst.tendsto x).comp tendsto_snd)).2 _ hxr₁,
      (tendsto_order.mp ((continuous_snd.tendsto x).comp tendsto_snd)).2 _ hxr₂]
      with n hn hn₁ hn₂
    exact (hf n.1 ⟨hn₁.le, hn₂.le⟩).trans_lt hn

theorem monotone_joint_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → Point → I) (hf : ∀ n i, Monotone (f n i)) :
    ∃ (φ : ℕ → ℕ) (F : ι → Point → I), StrictMono φ ∧
      (∀ i, Monotone (F i) ∧ Measurable (F i)) ∧
      (∀ i x, ContinuousAt (F i) x →
        Tendsto (fun q : ℕ × Point => f (φ q.1) i q.2)
          (atTop ×ˢ 𝓝 x) (𝓝 (F i x))) := by
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq
    (fun n i q => f n i (ratPoint q))
  refine ⟨φ, fun i => lowerGrid (g i), hφ,
    fun i => ⟨lowerGrid_monotone _, lowerGrid_measurable _⟩, ?_⟩
  intro i x hx
  apply joint_tendsto_of_grid (fun n => hf (φ n) i) _ hx
  intro q
  exact ((tendsto_pi_nhds.mp hg) i).apply_nhds q

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows
open scoped Topology unitInterval

def signedPair (before : Bool) (p : Point) : Point :=
  if before then (p.1, -p.2) else (-p.1, p.2)

lemma continuous_signedPair (b : Bool) : Continuous (signedPair b) := by
  cases b
  · exact continuous_fst.neg.prodMk continuous_snd
  · exact continuous_fst.prodMk continuous_snd.neg

lemma signedPair_involutive (b : Bool) : Function.Involutive (signedPair b) := by
  intro p
  cases b <;> simp [signedPair]

noncomputable def pairCoordinates (b : Bool) (A B : Window) (z : Labels) : Point :=
  signedPair b (z A, z B)

lemma continuous_pairCoordinates (b : Bool) (A B : Window) :
    Continuous (pairCoordinates b A B) :=
  (continuous_signedPair b).comp ((continuous_subtype_val.comp (continuous_apply A)).prodMk
    (continuous_subtype_val.comp (continuous_apply B)))

noncomputable def Configuration.extendedRank (F : Configuration) (b : Bool) (A B C : Window) :
    Point → I := RankLimit.extendRank (fun p => pairCoordinates b A B (F.system.labels F.generic p))
      (fun p => F.system.labels F.generic p C)

lemma Configuration.extendedRank_monotone (F : Configuration) (b : Bool) (A B C : Window) :
    Monotone (F.extendedRank b A B C) := RankLimit.extendRank_monotone _ _

lemma Configuration.extendedRank_eq (F : Configuration) (b : Bool) {A B C : Window}
    (hAB : Before A B)
    (hC : if b then Before C A ∧ Before C B else Before A C ∧ Before B C)
    (hA : 0 < length F.R A) (hB : 0 < length F.R B) (hCl : 0 < length F.R C)
    (p : Point) :
    F.extendedRank b A B C (pairCoordinates b A B (F.system.labels F.generic p)) =
      F.system.labels F.generic p C := by
  apply RankLimit.extendRank_eq
  intro x y hxy
  let H := F.system.rankHomeomorph F.generic hAB hA hB
  have hx := F.system.rankHomeomorph_coordinates F.generic hAB hA hB x
  have hy := F.system.rankHomeomorph_coordinates F.generic hAB hA hB y
  change ((F.system.labels F.generic x C : I) : ℝ) ≤ (F.system.labels F.generic y C : ℝ)
  have he (q : Point) : F.system.rankInCoordinates F.generic hAB hA hB C (H q) =
      (F.system.labels F.generic q C : ℝ) := by
    simp only [Batches.System.rankInCoordinates, H, Homeomorph.symm_apply_apply]
  rw [← he x, ← he y]
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hC
    have hm := F.system.rankInCoordinates_after F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H y).1 ≤ (H x).1 ∧ (H x).2 ≤ (H y).2 := by
      change ((H y).1 : ℝ) ≤ ((H x).1 : ℝ) ∧ ((H x).2 : ℝ) ≤ ((H y).2 : ℝ)
      rw [hy.1,hx.1,hx.2,hy.2]
      simpa only [pairCoordinates, signedPair, Bool.false_eq_true, ite_false, Prod.mk_le_mk,
        neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)
  · simp only [ite_true] at hC
    have hm := F.system.rankInCoordinates_before F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H x).1 ≤ (H y).1 ∧ (H y).2 ≤ (H x).2 := by
      change ((H x).1 : ℝ) ≤ ((H y).1 : ℝ) ∧ ((H y).2 : ℝ) ≤ ((H x).2 : ℝ)
      rw [hx.1,hy.1,hy.2,hx.2]
      simpa only [pairCoordinates, signedPair, ite_true, Prod.mk_le_mk,neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)

end PlanarHalving.RankLimits

namespace PlanarHalving.Limits
open Set Filter MeasureTheory Metric
open scoped Topology

lemma support_coordinate_identity {X Y T : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [MetricSpace T]
    {μs : ℕ → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : X → Y) (hp : Continuous p)
    (c : X → T) (hc : Continuous c) (f : ℕ → Y → T)
    (hid : ∀ᶠ n in atTop, ∀ᵐ z ∂(μs n : Measure X), c z = f n (p z))
    {z : X} (hz : z ∈ (μ : Measure X).support) {v : T}
    (hf : Tendsto (fun q : ℕ × Y => f q.1 q.2) (atTop ×ˢ 𝓝 (p z)) (𝓝 v)) :
    c z = v := by
  by_contra hne
  have hd : 0 < dist (c z) v := dist_pos.mpr hne
  have hp' : Tendsto (fun q : ℕ × X => (q.1,p q.2)) (atTop ×ˢ 𝓝 z)
      (atTop ×ˢ 𝓝 (p z)) := tendsto_fst.prodMk ((hp.tendsto z).comp tendsto_snd)
  have hdlim := ((hc.tendsto z).comp tendsto_snd).dist (hf.comp hp')
  have he := (tendsto_order.mp hdlim).1 0 hd
  obtain ⟨pa,hpa,pb,hpb,hbad⟩ := Filter.eventually_prod_iff.mp he
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hpb
  let : Nonempty X := ⟨z⟩
  have hpos : 0 < (μ (ball z (r/2)) : ℝ) := by
    have hh := (Measure.mem_support_iff_forall z).mp hz _ (ball_mem_nhds _ (half_pos hr))
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
    exact_mod_cast hh
  have helow := eventually_thickening_lower hμ (ball z (r/2)) (half_pos hr) hpos
  obtain ⟨n,hn,hni,hnlow⟩ := (hpa.and (hid.and helow)).exists
  have hzero : (μs n : Measure X) (ball z r) = 0 := by
    apply measure_mono_null (t := {w | c w ≠ f n (p w)})
    · intro w hw
      exact dist_pos.mp (hbad hn (hball hw))
    · exact ae_iff.mp hni
  have hsub : thickening (r/2) (ball z (r/2)) ⊆ ball z r := by
    simpa only [add_halves] using thickening_ball z (r/2) (r/2)
  have hzero' := measure_mono_null hsub hzero
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_eq_zero] at hzero'
  rw [hzero'] at hnlow
  exact (lt_irrefl (0 : ℝ)) hnlow

end PlanarHalving.Limits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Limits
open scoped Topology unitInterval

lemma Configuration.points_ae (F : Configuration) (H : Labels → Prop)
    (hH : ∀ p, H (F.label p)) : ∀ᵐ z ∂(F.points : Measure Labels), H z := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq,Filter.eventually_pure,Function.comp_apply] using hH (F.point i)

lemma Converges.subseq {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : Converges (F ∘ φ) L :=
  ⟨h.points.comp hφ.tendsto_atTop,fun J => (h.vertices J).comp hφ.tendsto_atTop,
    h.edgeTime.comp hφ.tendsto_atTop,fun J => (h.timeRestrict J).comp hφ.tendsto_atTop,
    fun A B => (h.crossings A B).comp hφ.tendsto_atTop⟩

theorem Converges.rank_analytic {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (b : Bool) {A B : Window} (hAB : Before A B)
    {ι : Type*} [Countable ι] (C : ι → Window)
    (hC : ∀ i, if b then Before (C i) A ∧ Before (C i) B else Before A (C i) ∧ Before B (C i)) :
    ∃ (φ : ℕ → ℕ) (G : ι → Point → I), StrictMono φ ∧
      (∀ i, Monotone (G i) ∧ Measurable (G i)) ∧
      (∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p) ∧
      (∀ i z, z ∈ (L.points : Measure Labels).support →
        ContinuousAt (G i) (pairCoordinates b A B z) →
        z (C i) = G i (pairCoordinates b A B z)) ∧
      (∀ i p, ContinuousAt (G i) p →
        Tendsto (fun q : ℕ × Point => (F (φ q.1)).extendedRank b A B (C i) q.2)
          (atTop ×ˢ 𝓝 p) (𝓝 (G i p))) := by
  obtain ⟨φ,G,hφ,hG,hlim⟩ := RankLimit.monotone_joint_subsequence
    (fun n i => (F n).extendedRank b A B (C i)) (fun n i => (F n).extendedRank_monotone b A B (C i))
  refine ⟨φ,G,hφ,hG,?_,?_,hlim⟩
  · intro i
    apply Calculus.bounded_monotone_ae_differentiable (fun x y hxy => (hG i).1 hxy)
      (measurable_subtype_coe.comp (hG i).2) (B:=1)
    intro x
    simpa only [Real.norm_eq_abs,abs_of_nonneg (G i x).property.1] using (G i x).property.2
  · intro i z hz hcont
    apply support_coordinate_identity (h.subseq hφ).points (pairCoordinates b A B)
      (continuous_pairCoordinates b A B) (fun z => z (C i)) (continuous_apply (C i))
      (fun n => (F (φ n)).extendedRank b A B (C i)) _ hz (hlim i _ hcont)
    have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
    filter_upwards [eventually_length_pos _ hR' A,eventually_length_pos _ hR' B,
      eventually_length_pos _ hR' (C i)] with n hnA hnB hnC
    apply Configuration.points_ae
    intro p
    exact ((F (φ n)).extendedRank_eq b hAB (hC i) hnA hnB hnC p).symm

end PlanarHalving.RankLimits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma positive_single_component {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X) [∀ i, IsFiniteMeasure (ν i)]
    (hμ : μ ≪ Measure.sum ν) (hpos : μ univ ≠ 0) :
    ∃ (i : ι) (A : Set X), MeasurableSet A ∧ μ A ≠ 0 ∧ μ.restrict A ≪ ν i := by
  classical
  choose A hA hsing hν using fun i => Measure.mutuallySingular_singularPart μ (ν i)
  have hac (i : ι) : μ.restrict (A i) ≪ ν i := by
    apply Measure.AbsolutelyContinuous.mk
    intro B hB hzero
    rw [Measure.restrict_apply hB,μ.haveLebesgueDecomposition_add (ν i),Measure.add_apply]
    rw [measure_mono_null inter_subset_right (hsing i),zero_add]
    exact withDensity_absolutelyContinuous (ν i) _
      (measure_mono_null inter_subset_left hzero)
  have hnull : μ (⋃ i, A i)ᶜ = 0 := by
    apply hμ
    rw [Measure.sum_apply_eq_zero]
    intro i
    exact measure_mono_null (compl_subset_compl.mpr (subset_iUnion A i)) (hν i)
  obtain ⟨i,hi⟩ : ∃ i, μ (A i) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hU : μ (⋃ i, A i) = 0 := measure_iUnion_null hh
    exact hpos (by simpa only [union_compl_self] using measure_union_null hU hnull)
  exact ⟨i,A i,hA i,hi,hac i⟩

lemma restrict_ac_withDensity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f) {A : Set X} (_hA : MeasurableSet A)
    (hpos : ∀ x ∈ A, f x ≠ 0) : μ.restrict A ≪ μ.withDensity f := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hzero
  rw [Measure.restrict_apply hB]
  have hh := (withDensity_apply_eq_zero hf).mp hzero
  apply measure_mono_null (t := {x | f x ≠ 0} ∩ B)
  · intro x hx
    exact ⟨hpos x hx.2,hx.1⟩
  · exact hh

end PlanarHalving.Limits

end OAI
