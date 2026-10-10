import OAI.Combinatorics.HalvingLines.WindowMeasures

namespace OAI

open Filter Topology

namespace PlanarHalving
lemma card_filter_attached {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : ↥s => p x.val)).card = (s.filter p).card := by
  classical
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext x
  simp [and_comm]
end PlanarHalving
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def Configuration.longEdges (F : Configuration) (ρ : ℝ) : Finset (Fin F.n×Fin F.n) :=
  F.system.edges.filter (fun e => ENNReal.ofReal ρ ≤ Metric.ediam
    (F.label '' segment ℝ (F.point e.1) (F.point e.2)))

lemma Configuration.longEdges_bound {ρ : ℝ} (hρ : 0<ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Configuration, ((F.longEdges ρ).card : ℝ) ≤ C*(F.a : ℝ)*F.n := by
  classical
  obtain ⟨K,hK⟩ := CompactLabels.finite_tail (ι:=Window) (ENNReal.ofReal_pos.mpr hρ)
  refine ⟨4*K.card/ρ,by positivity,fun F => ?_⟩
  have hh := CompactLabels.long_count_bound F.label
    (fun e : ↥F.system.edges => segment ℝ (F.point e.val.1) (F.point e.val.2))
    (ENNReal.ofReal_pos.mpr hρ) K hK (fun J => F.system.coordinate_oscillation F.generic J)
  have hh' := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_ofReal hρ.le,
    ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at hh'
  have hc : (Finset.univ.filter (fun e : ↥F.system.edges => ENNReal.ofReal ρ ≤ Metric.ediam
      (F.label '' segment ℝ (F.point e.val.1) (F.point e.val.2)))).card=(F.longEdges ρ).card :=
    by
      simpa only [Configuration.longEdges] using (card_filter_attached F.system.edges
        (fun e => ENNReal.ofReal ρ ≤ Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2))))
  rw [hc] at hh'
  change ρ/2*((F.longEdges ρ).card : ℝ) ≤ (K.card : ℝ)*(2*(F.a : ℝ)*F.n) at hh'
  calc
    _  ≤  4*(K.card : ℝ)*F.a*F.n/ρ := (le_div_iff₀ hρ).mpr (by nlinarith [hh'])
    _ = _ := by ring

lemma longEdges_ratio_zero {F : ℕ → Configuration}
    (hratio : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0<ρ) :
    Tendsto (fun n => (((F n).longEdges ρ).card : ℝ)/((F n).R*(F n).a^2)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := Configuration.longEdges_bound hρ
  have ht := hratio.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro n
  have ha : (0:ℝ)<(F n).a := Nat.cast_pos.mpr (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  apply (div_le_iff₀ (mul_pos hR (pow_pos ha 2))).mpr
  have hh := hbound (F n)
  calc
    _  ≤  C*(F n).a*(F n).n := hh
    _ = _ := by field_simp

lemma Configuration.short_edge_label {F : Configuration} {ρ : ℝ}
    {e : Fin F.n×Fin F.n} (he : e∈F.system.edges) (hshort : e∉F.longEdges ρ)
    {p : Point} (hp : p∈segment ℝ (F.point e.1) (F.point e.2)) :
    dist (F.label p) (F.label (F.point e.1))<ρ := by
  classical
  have hdiam : Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2))<ENNReal.ofReal ρ := by
    have hh : ¬ ENNReal.ofReal ρ ≤ Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2)) := by
      intro hh
      exact hshort (Finset.mem_filter.mpr ⟨he,hh⟩)
    exact lt_of_not_ge hh
  have hh : edist (F.label p) (F.label (F.point e.1))<ENNReal.ofReal ρ :=
    (Metric.edist_le_ediam_of_mem (s := F.label '' segment ℝ (F.point e.1) (F.point e.2))
      ⟨p,hp,rfl⟩ ⟨F.point e.1,left_mem_segment ℝ _ _,rfl⟩).trans_lt hdiam
  rw [edist_dist] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hh).1

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma eventually_lt_closed {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {F : Set X} (hF : IsClosed F)
    {q : ℝ} (hq : (μ F : ℝ)<q) : ∀ᶠ n in atTop, (μs n F : ℝ)<q := by
  have hq0 : 0<q := lt_of_le_of_lt (NNReal.coe_nonneg _) hq
  have hq' : (μ : Measure X) F<ENNReal.ofReal q := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).mpr hq
  have ht := (FiniteMeasure.limsup_measure_closed_le_of_tendsto h hF).trans_lt hq'
  have he := eventually_lt_of_limsup_lt ht
  filter_upwards [he] with n hn
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff hq0).mp (by simpa only [ENNReal.ofReal_coe_nnreal] using hn)

lemma eventually_thickening_lower [Nonempty X]
    {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) (F : Set X) {r : ℝ} (hr : 0<r)
    {q : ℝ} (hq : q<(μ F : ℝ)) :
    ∀ᶠ n in atTop, q<(μs n (Metric.thickening r F) : ℝ) := by
  obtain ⟨s,hs,hnull⟩ := exists_null_frontiers_thickening (μ : Measure X) F
  obtain ⟨j,hj⟩ := ((tendsto_order.mp hs).2 r hr).exists
  have hlim := NNReal.continuous_coe.tendsto _ |>.comp
    (finiteMeasure_tendsto_apply h (hnull j).2)
  have hb : q<(μ (Metric.thickening (s j) F) : ℝ) :=
    hq.trans_le (NNReal.coe_le_coe.mpr (μ.apply_mono (Metric.self_subset_thickening (hnull j).1 _)))
  filter_upwards [(tendsto_order.mp hlim).1 q hb] with n hn
  exact hn.trans_le (NNReal.coe_le_coe.mpr (μs n |>.apply_mono (Metric.thickening_mono hj.le _)))

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Configuration.edgeWindow_apply (F : Configuration) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (F.edgeWindow J U : ℝ)=
      (((F.system.timeWindow J).edges.filter (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U)).card : ℝ)/
        ((F.R : ℝ)*F.a^2) := by
  classical
  rw [F.edgeWindow_eq,System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
  simp only [Function.comp_apply]
  rw [card_filter_attached _ (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U)]
  simp only [NNReal.coe_inv,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast,
    div_eq_inv_mul]

lemma Configuration.windows_edges_disjoint (F : Configuration) {A B : Window}
    (hAB : Disjoint (carrier A) (carrier B)) :
    Disjoint (F.system.timeWindow A).edges (F.system.timeWindow B).edges := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  let v : ↥F.system.edges := ⟨e,F.system.timeWindow_edges A heA⟩
  exact Set.disjoint_left.mp hAB ((F.system.timeWindow_mem A v).mp heA)
    ((F.system.timeWindow_mem B v).mp heB)

noncomputable def Configuration.selectedEdges (F : Configuration) (W : Finset Window)
    (U : Set Labels) : Finset (Fin F.n×Fin F.n) := by
  classical
  exact W.biUnion (fun J => (F.system.timeWindow J).edges.filter (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U))

lemma Configuration.selectedEdges_mass (F : Configuration) (W : Finset Window)
    (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {U : Set Labels} (hU : MeasurableSet U) :
    ∑ J∈W, (F.edgeWindow J U : ℝ) =
      ((F.selectedEdges W U).card : ℝ)/((F.R : ℝ)*F.a^2) := by
  classical
  simp_rw [F.edgeWindow_apply _ hU]
  rw [← Finset.sum_div,Configuration.selectedEdges,Finset.card_biUnion]
  · push_cast; rfl
  · intro J hJ K hK hJK
    exact (F.windows_edges_disjoint (hW J hJ K hK hJK)).mono
      (Finset.filter_subset ..) (Finset.filter_subset ..)

lemma Configuration.selectedEdges_subset (F : Configuration) (W : Finset Window)
    (U : Set Labels) : F.selectedEdges W U⊆F.system.edges := by
  classical
  intro e he
  obtain ⟨J,_hJ,heJ⟩ := Finset.mem_biUnion.mp he
  exact F.system.timeWindow_edges J (Finset.mem_filter.mp heJ).1

lemma Configuration.retained_near (F : Configuration) (W : Finset Window)
    (A : Set Labels) {ρ : ℝ} (e : Fin F.n×Fin F.n)
    (he : e∈F.selectedEdges W (Metric.thickening ρ A) \ F.longEdges ρ)
    (p : Point) (hp : p∈segment ℝ (F.point e.1) (F.point e.2)) :
    F.label p∈Metric.cthickening (2*ρ) A := by
  classical
  obtain ⟨hes,hel⟩ := Finset.mem_sdiff.mp he
  obtain ⟨J,_hJ,heJ⟩ := Finset.mem_biUnion.mp hes
  obtain ⟨z,hz,hd⟩ := Metric.mem_thickening_iff.mp (Finset.mem_filter.mp heJ).2
  have hp' := F.short_edge_label (F.selectedEdges_subset W _ hes) hel hp
  exact Metric.mem_cthickening_of_dist_le _ z _ A hz
    (le_of_lt ((dist_triangle _ _ _).trans_lt (by linarith)))

lemma Configuration.retained_mass_lower (F : Configuration) (W : Finset Window)
    (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {U : Set Labels} (hU : MeasurableSet U) (ρ : ℝ) :
    (∑ J∈W, (F.edgeWindow J U : ℝ)) -
        ((F.longEdges ρ).card : ℝ)/((F.R : ℝ)*F.a^2)  ≤
      ((F.selectedEdges W U \ F.longEdges ρ).card : ℝ)/((F.R : ℝ)*F.a^2) := by
  classical
  rw [F.selectedEdges_mass W hW hU,← sub_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := Finset.card_le_card (show F.selectedEdges W U⊆
      (F.selectedEdges W U \ F.longEdges ρ)∪F.longEdges ρ from by
        intro e he; by_cases h : e∈F.longEdges ρ <;> simp [he,h])
  have hh' := hh.trans (Finset.card_union_le _ _)
  have hh'' : ((F.selectedEdges W U).card : ℝ) ≤
      ((F.selectedEdges W U \ F.longEdges ρ).card : ℝ)+(F.longEdges ρ).card := by
    exact_mod_cast hh'
  linarith

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open Filter
open scoped Topology

lemma eventually_sum_lower {ι : Type*} (W : Finset ι) {f : ℕ → ι → ℝ} {a : ι → ℝ}
    (h : ∀ i∈W, ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, a i-ε ≤ f n i)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n in atTop, (∑ i∈W, a i)-ε ≤ ∑ i∈W, f n i := by
  classical
  induction W using Finset.induction_on generalizing ε with
  | empty => exact Eventually.of_forall (fun _ => by simpa using hε.le)
  | @insert i W hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _) (ε/2) (by positivity)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) (ε := ε/2) (half_pos hε)
    filter_upwards [h₁,h₂] with n hn hn'
    simp only [Finset.sum_insert hi]
    linarith

lemma eventually_sum_upper {ι : Type*} (W : Finset ι) {f : ℕ → ι → ℝ} {a : ι → ℝ}
    (h : ∀ i∈W, ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, f n i ≤ a i+ε)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n in atTop, (∑ i∈W, f n i) ≤ (∑ i∈W, a i)+ε := by
  have hh := eventually_sum_lower W (f:=fun n i => -f n i) (a:=fun i => -a i)
    (fun i hi δ hδ => (h i hi δ hδ).mono (fun n hn => by linarith)) hε
  filter_upwards [hh] with n hn
  simp only [Finset.sum_neg_distrib] at hn
  linarith

lemma cubic_of_eventual_bounds {x b e : ℕ → ℝ} {s B C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hx : ∀ n, 0 ≤ x n)
    (hb : ∀ n, (x n)^3 ≤ C*b n+e n)
    (hlower : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, s-ε ≤ x n)
    (hupper : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, b n ≤ B+ε)
    (he : Tendsto e atTop (𝓝 0)) : s^3 ≤ C*B := by
  have hineq (ε : ℝ) (hε : 0<ε) : (max (s-ε) 0)^3 ≤ C*(B+ε)+ε := by
    have hev := ((tendsto_order.mp he).2 ε hε).mono (fun n hn => hn.le)
    obtain ⟨n,hn,hn',hen⟩ := ((hlower ε hε).and ((hupper ε hε).and hev)).exists
    have hl : max (s-ε) 0 ≤ x n := max_le hn (hx n)
    exact (pow_le_pow_left₀ (le_max_right _ _) hl 3).trans
      ((hb n).trans (add_le_add (mul_le_mul_of_nonneg_left hn' hC) hen))
  have hlim₁ : Tendsto (fun ε : ℝ => (max (s-ε) 0)^3) (𝓝[>] 0) (𝓝 (s^3)) := by
    have hc : Continuous (fun ε : ℝ => (max (s-ε) 0)^3) := by fun_prop
    simpa only [sub_zero,max_eq_left hs] using (hc.continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)).tendsto
  have hlim₂ : Tendsto (fun ε : ℝ => C*(B+ε)+ε) (𝓝[>] 0) (𝓝 (C*B)) := by
    have hc : Continuous (fun ε : ℝ => C*(B+ε)+ε) := by fun_prop
    simpa only [add_zero] using (hc.continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)).tendsto
  exact le_of_tendsto_of_tendsto hlim₁ hlim₂
    (Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε => hineq ε hε))

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Configuration.retained_cubic (F : Configuration) {C : ℝ}
    (hcoeff : 4608*(F.a : ℝ)^2*F.n^4/((F.R : ℝ)*F.a^2)^3 ≤ C)
    (W : Finset Window) (E : Finset (Fin F.n×Fin F.n)) (hE : E⊆F.system.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(F.system.timeWindow J).edges)
    {U : Set Labels} (hU : MeasurableSet U)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (F.point e.1) (F.point e.2), F.label p∈U) :
    ((E.card : ℝ)/((F.R : ℝ)*F.a^2))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((F.vertices J).mass : ℝ)^2
        else (F.crossings J K U : ℝ))+
      13824*(F.n : ℝ)^3/((F.R : ℝ)*F.a^2)^3 := by
  classical
  let cr : ℝ := ((F.system.drawing.restrictEdges E).crossings.card : ℝ)
  let coeff : ℝ := 4608*(F.a : ℝ)^2*F.n^4/((F.R : ℝ)*F.a^2)^3
  have hc := F.system.restricted_crossing F.generic E hE
  have hc' : (E.card : ℝ)^3 ≤ 4608*(F.n : ℝ)^2*cr+13824*(F.n : ℝ)^3 := by
    dsimp [cr]; nlinarith [mul_nonneg (sq_nonneg (F.n : ℝ))
      (show (0:ℝ) ≤ ((F.system.drawing.restrictEdges E).crossings.card : ℝ) by positivity)]
  have hn : (F.n : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.n)
  have ha : (F.a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.a)
  have hR : (F.R : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.R)
  have heq : (4608*(F.n : ℝ)^2*cr+13824*(F.n : ℝ)^3)/((F.R : ℝ)*F.a^2)^3 =
      coeff*(cr/((F.a : ℝ)*F.n)^2)+13824*(F.n : ℝ)^3/((F.R : ℝ)*F.a^2)^3 := by
    dsimp [coeff]; field_simp
  have hb := F.system.retained_crossing_bound F.generic F.label hU W E hE hcover hnear
  have hb' : cr/((F.a : ℝ)*F.n)^2 ≤
      ∑ J∈W, ∑ K∈W, if J=K then 2*((F.vertices J).mass : ℝ)^2 else (F.crossings J K U : ℝ) := by
    simpa only [F.vertices_mass_ratio,div_pow,mul_div_assoc,Configuration.crossings,Nat.cast_mul] using hb
  rw [div_pow]
  apply (div_le_div_of_nonneg_right hc' (by positivity)).trans
  rw [heq]
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_right hcoeff (by dsimp [cr]; positivity)).trans
    (mul_le_mul_of_nonneg_left hb' ((show (0:ℝ) ≤ coeff by dsimp [coeff]; positivity).trans hcoeff))

lemma Converges.partition_cubic_thickening {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (W : Finset Window) (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    (A : Set Labels) {ρ : ℝ} (hρ : 0<ρ) :
    (∑ J∈W, (L.edgeWindow J A : ℝ))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2
        else (L.crossings J K (Metric.cthickening (2*ρ) A) : ℝ)) := by
  classical
  let U := Metric.thickening ρ A
  let V := Metric.cthickening (2*ρ) A
  let E (n : ℕ) := (F n).selectedEdges W U \ (F n).longEdges ρ
  apply cubic_of_eventual_bounds (x:=fun n => ((E n).card : ℝ)/((F n).R*(F n).a^2))
    (b:=fun n => ∑ J∈W, ∑ K∈W, if J=K then 2*(((F n).vertices J).mass : ℝ)^2
      else ((F n).crossings J K V : ℝ))
    (by positivity) hC (fun n => by positivity)
  · intro n
    apply (F n).retained_cubic (hcoeff n) W (E n)
      ((Finset.sdiff_subset).trans ((F n).selectedEdges_subset W U))
    · intro e he
      obtain ⟨J,hJ,heJ⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp he).1
      exact ⟨J,hJ,(Finset.mem_filter.mp heJ).1⟩
    · exact Metric.isClosed_cthickening.measurableSet
    · exact fun e he p hp => (F n).retained_near W A e he p hp
  · intro ε hε
    have h₁ := eventually_sum_lower W (fun J _ δ hδ =>
      (eventually_thickening_lower (h.edgeWindow J) A hρ (by linarith : (L.edgeWindow J A : ℝ)-δ<_)).mono
        (fun _ hn => hn.le)) (half_pos hε)
    have h₂ := (tendsto_order.mp (longEdges_ratio_zero hshort hρ)).2 (ε/2) (half_pos hε)
    filter_upwards [h₁,h₂] with n hn hn'
    have hb := (F n).retained_mass_lower W hW (U:=U) Metric.isOpen_thickening.measurableSet ρ
    dsimp only [E,U] at *
    linarith
  · intro ε hε
    apply eventually_sum_upper W _ hε
    intro J _ δ hδ
    apply eventually_sum_upper W _ hδ
    intro K _ τ hτ
    by_cases hJK : J=K
    · simp only [ite_eq_left hJK]
      have ht := NNReal.continuous_coe.tendsto _ |>.comp (FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices J))
      exact ((tendsto_order.mp (ht.pow 2 |>.const_mul 2)).2 _ (lt_add_of_pos_right _ hτ)).mono (fun _ hn => hn.le)
    · simp only [ite_eq_right hJK]
      exact (eventually_lt_closed (h.crossings J K) Metric.isClosed_cthickening
        (lt_add_of_pos_right _ hτ)).mono (fun _ hn => hn.le)
  · exact herror

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma finiteMeasure_tendsto_cthickening (μ : FiniteMeasure X) {A : Set X} (hA : IsClosed A)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => (μ (Metric.cthickening (r n) A) : ℝ)) atTop (𝓝 (μ A : ℝ)) := by
  have ht := tendsto_measure_cthickening_of_isClosed (μ:=(μ : Measure X))
    ⟨1,by norm_num,measure_ne_top _ _⟩ hA
  exact ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) A) |>.comp (ht.comp hr)

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Data.partitionQuantity_tendsto (L : Data) (W : Finset Window)
    {A : Set Labels} (hA : IsClosed A) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2
        else (L.crossings J K (Metric.cthickening (r n) A) : ℝ)) atTop
      (𝓝 (∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J K A : ℝ))) := by
  classical
  apply tendsto_finsetSum
  intro J hJ
  apply tendsto_finsetSum
  intro K hK
  by_cases hJK : J=K
  · simp only [ite_eq_left hJK]; exact tendsto_const_nhds
  · simp only [ite_eq_right hJK]; exact finiteMeasure_tendsto_cthickening _ hA hr

lemma Converges.partition_cubic_closed {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (W : Finset Window) (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {A : Set Labels} (hA : IsClosed A) :
    (∑ J∈W, (L.edgeWindow J A : ℝ))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J K A : ℝ)) := by
  classical
  have hr : Tendsto (fun n : ℕ => 2*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  have hlim := L.partitionQuantity_tendsto W hA hr |>.const_mul C
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun n =>
    h.partition_cubic_thickening hC hcoeff herror hshort W hW A (by positivity : 0 < (1/((n:ℝ)+1))))

end PlanarHalving.RankLimits
namespace PlanarHalving.UniformPartition
open Set
open scoped unitInterval

lemma cell_refinement (m d : ℕ) [NeZero m] [NeZero d] (i : Fin (m*d)) :
    cell (m*d) i ⊆ cell m ⟨i.val/d,(Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr i.isLt⟩ := by
  intro t ht
  let j : Fin m := ⟨i.val/d,(Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr i.isLt⟩
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hd : (0:ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hlo : (j:ℝ)*d ≤ (i:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self i.val d
  have hhi : (i:ℝ)+1 ≤ ((j:ℝ)+1)*d := by
    have hr := Nat.mod_lt i.val (NeZero.pos d)
    have he := Nat.mod_add_div i.val d
    have hh : i.val+1 ≤ (i.val/d+1)*d := by nlinarith
    exact_mod_cast hh
  have hlow : (j:ℝ)/(m:ℝ) ≤ (t:ℝ) := by
    apply le_trans _ (cell_lower (m*d) i ht)
    rw [Nat.cast_mul]
    apply (div_le_div_iff₀ hm (mul_pos hm hd)).mpr
    nlinarith
  have hup : ((i:ℝ)+1)/((m*d:ℕ):ℝ) ≤ ((j:ℝ)+1)/(m:ℝ) := by
    rw [Nat.cast_mul]
    apply (div_le_div_iff₀ (mul_pos hm hd) hm).mpr
    nlinarith
  change t∈cell m j
  unfold cell
  split_ifs with hj
  · refine ⟨hlow,?_⟩
    change (t:ℝ) ≤ _
    simpa only [boundary,Fin.val_succ,Nat.cast_add,Nat.cast_one] using (cell_upper (m*d) i ht).trans hup
  · have hi : i.val+1≠m*d := by
      intro hi
      have hsur : i.val+1 ≤ (j.val+1)*d := by exact_mod_cast hhi
      have hjlt : j.val+1 < m := by omega
      have hh := Nat.mul_lt_mul_of_pos_right hjlt (NeZero.pos d)
      omega
    refine ⟨hlow,?_⟩
    change (t:ℝ) < _
    simpa only [boundary,Fin.val_succ,Nat.cast_add,Nat.cast_one] using (cell_upper_lt (m*d) i hi ht).trans_le hup

lemma exists_cell_refinement (m d N : ℕ) [NeZero m] [NeZero d] [NeZero N]
    (hN : N=m*d) (i : Fin N) : ∃ j : Fin m, cell N i⊆cell m j := by
  subst N
  exact ⟨_,cell_refinement m d i⟩

end PlanarHalving.UniformPartition
namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval

lemma carrier_refinement (d m : ℕ) (i : Fin (2^(d+m))) :
    ∃ j : Fin (2^d), carrier ⟨d+m,i⟩⊆carrier ⟨d,j⟩ := by
  exact UniformPartition.exists_cell_refinement (2^d) (2^m) (2^(d+m)) (pow_add 2 d m) i

lemma same_depth_disjoint {d : ℕ} {i j : Fin (2^d)} (hij : i≠j) :
    Disjoint (carrier ⟨d,i⟩) (carrier ⟨d,j⟩) := UniformPartition.cells_disjoint _ hij

lemma refining_cell_subset {K J : Window} {m : ℕ} (hdepth : J.1=K.1+m)
    {t : I} (htK : t∈carrier K) (htJ : t∈carrier J) : carrier J⊆carrier K := by
  obtain ⟨d,i⟩ := K
  obtain ⟨e,j⟩ := J
  dsimp only at hdepth
  subst e
  obtain ⟨k,hk⟩ := carrier_refinement d m j
  by_cases hki : k=i
  · simpa only [hki] using hk
  · exact False.elim (Set.disjoint_left.mp (same_depth_disjoint hki) (hk htJ) htK)

end PlanarHalving.TimeWindows
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def localPartition (K : Window) (m : ℕ) : Finset Window :=
  (timePartition (K.1+m)).filter (fun J => carrier J⊆carrier K)

lemma mem_timePartition {J : Window} {m : ℕ} : J∈timePartition m ↔ J.1=m := by
  obtain ⟨d,i⟩ := J
  constructor
  · intro h
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp h
    exact (congrArg Sigma.fst he).symm
  · intro h
    dsimp only at h
    subst d
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma timePartition_disjoint (m : ℕ) {J K : Window} (hJ : J∈timePartition m) (hK : K∈timePartition m)
    (hJK : J≠K) : Disjoint (carrier J) (carrier K) := by
  obtain ⟨d,i⟩ := J
  obtain ⟨e,j⟩ := K
  have hd := mem_timePartition.mp hJ
  have he := mem_timePartition.mp hK
  dsimp only at hd he
  subst d; subst e
  exact same_depth_disjoint (fun hij => hJK (congrArg (Sigma.mk m) hij))

lemma localPartition_cover (K : Window) (m : ℕ) {t : I} (ht : t∈carrier K) :
    ∃ J∈localPartition K m, t∈carrier J := by
  obtain ⟨J,hJ,htJ⟩ := timePartition_cover (K.1+m) t
  exact ⟨J,Finset.mem_filter.mpr ⟨hJ,refining_cell_subset (mem_timePartition.mp hJ) ht htJ⟩,htJ⟩

lemma localPartition_disjoint (K : Window) (m : ℕ) {J H : Window}
    (hJ : J∈localPartition K m) (hH : H∈localPartition K m) (hJH : J≠H) :
    Disjoint (carrier J) (carrier H) :=
  timePartition_disjoint _ (Finset.mem_filter.mp hJ).1 (Finset.mem_filter.mp hH).1 hJH

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Converges.edgeWindow_apply {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)=(L.edgeTime : Measure (Labels×I)).real (U×ˢcarrier J) := by
  change ((L.edgeWindow J : Measure Labels) U).toReal= _
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

lemma Converges.localPartition_sum {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (K : Window) (m : ℕ)
    {U : Set Labels} (hU : MeasurableSet U) :
    ∑ J∈localPartition K m, (L.edgeWindow J U : ℝ)=(L.edgeWindow K U : ℝ) := by
  simp_rw [h.edgeWindow_apply hR _ hU]
  have hd : Set.PairwiseDisjoint (↑(localPartition K m) : Set Window) (fun J => U×ˢcarrier J) := by
    intro J hJ H hH hJH
    exact Set.disjoint_left.mpr (fun t htJ htH =>
      Set.disjoint_left.mp (localPartition_disjoint K m hJ hH hJH) htJ.2 htH.2)
  rw [← measureReal_biUnion_finset hd (fun J _ => hU.prod (measurable_carrier J))]
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨J,hJ,htJ⟩ := mem_iUnion₂.mp ht
    exact ⟨htJ.1,(Finset.mem_filter.mp hJ).2 htJ.2⟩
  · intro ht
    obtain ⟨J,hJ,htJ⟩ := localPartition_cover K m ht.2
    exact mem_iUnion₂.mpr ⟨J,hJ,ht.1,htJ⟩

end PlanarHalving.RankLimits

end OAI
