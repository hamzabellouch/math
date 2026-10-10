import OAI.Combinatorics.HalvingLines.ThinStrips

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set Filter MeasureTheory Batches TimeWindows RankLimits Enhancement Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma finite_window_params (F : Configuration) (K : Window) (E : Point ≃L[ℝ] Point)
    {A B l u : ℝ} (hA : 0 < A) (hB : 0 < B) (hlu : l < u)
    (h1 : E (1,0)=A • (1,l)) (h2 : E (0,1)=B • (1,u))
    (hspan : ∀ i, (F.system.timeWindow K).slope i ∈ Icc l u)
    (o : Point) {r : ℝ} (hr : 0 < r) :
    ∃ p : Subwindow K → CompactParams,
      (∀ J, (vertices F (physical E o r) J.val
        (Prod.snd ⁻¹' (encode '' awayStrips (p J).2.1.val (p J).2.2.1.val
          (fun i => ((p J).2.2.2 i).val))):ℝ) ≤ 2*(p J).1.val) ∧
      (∀ D : Finset (Subwindow K), Set.PairwiseDisjoint (↑D : Set (Subwindow K)) (fun J => carrier J.val) →
        (∑ J∈D, (p J).1.val) ≤ 4 ∧ (∑ J∈D, (p J).2.2.1.val) ≤ 1) := by
  classical
  let S := F.system.timeWindow K
  let pnt := fun v => physical E o r (F.point v)
  let j : Fin F.a := ⟨0,F.a_pos⟩
  let w : Fin (length F.R K) → ℝ := fun i => S.boundaryCount pnt j i
  let t : Fin (length F.R K+1) → ℝ := fun i => frameParameter A B l u (S.slope i)
  let s : Subwindow K → ℕ := fun J => start F.R J.val-start F.R K
  let m : Subwindow K → ℕ := fun J => length F.R J.val
  have hsm (J : Subwindow K) : s J+m J ≤ length F.R K := relative_end_le F.R J.property
  let b : Subwindow K → ℝ := fun J => (∑ i∈batchRange _ (s J) (m J), w i)/F.n
  let ti : Subwindow K → ℝ := fun J => t ⟨s J,by have := hsm J; omega⟩
  let theta : Subwindow K → ℝ := fun J => t ⟨s J+m J,by have := hsm J; omega⟩-ti J
  have hw (i) : 0 ≤ w i := Nat.cast_nonneg _
  have ht : Monotone t := by
    intro i i' hii'
    apply frameParameter_monotone hA hB hlu (hspan _) (hspan _)
    exact S.increasing.monotone hii'
  have htI (i) : t i ∈ Icc (0:ℝ) 1 := frameParameter_mem hA hB hlu (hspan _)
  have hcost : (∑ i, w i) ≤ 4*(F.n:ℝ) := by
    have hh := S.boundary_budget pnt j
      (fun v => (actual_tokens_monotone S E hA hB hlu h1 h2 hspan o hr j v).1)
      (fun v => (actual_tokens_monotone S E hA hB hlu h1 h2 hspan o hr j v).2)
    dsimp only [w]
    exact_mod_cast hh
  have hpos : 0 < (F.n:ℝ) := Nat.cast_pos.mpr F.n_pos
  have hb (J) : b J ∈ Icc (0:ℝ) 4 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => hw i)) hpos.le
    · apply (div_le_iff₀ hpos).mpr
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)).trans hcost
  have hti (J) : ti J ∈ Icc (0:ℝ) 1 := htI _
  have htheta (J) : theta J ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (ht (by simp [Fin.le_def]))
    · have hh := (htI (⟨s J+m J,by have := hsm J; omega⟩)).2
      have hh' := (hti J).1
      dsimp [theta]; linarith
  obtain ⟨c,hc,hfinite⟩ : ∃ c : Subwindow K → Fin 3 → ℝ,
      (∀ J h, c J h ∈ Icc (-4:ℝ) 4) ∧
      ∀ J, (((S.window (s J) (m J) (hsm J)).vertices.filter fun v =>
        pnt v∈awayStrips (ti J) (theta J) (c J)).card) ≤
          2*∑ i : Fin (m J), S.boundaryCount pnt j ⟨s J+i.val,by have := hsm J; omega⟩ := by
    choose c hc hb using fun J => S.window_boundary E hA hB hlu h1 h2 hspan o hr j (s J) (m J) (hsm J)
    refine ⟨c,hc,fun J => ?_⟩
    convert hb J using 1
    congr 1
    apply Finset.filter_congr
    intro v _
    rfl
  let p : Subwindow K → CompactParams := fun J =>
    (⟨b J,hb J⟩,⟨ti J,hti J⟩,⟨theta J,htheta J⟩,fun i => ⟨c J i,hc J i⟩)
  refine ⟨p,?_,?_⟩
  · intro J
    change (vertices F (physical E o r) J.val (Prod.snd ⁻¹' (encode '' awayStrips (ti J) (theta J) (c J))):ℝ) ≤ 2*b J
    rw [vertices,System.vertexMeasure_apply _ _ ((isOpenMap_encode _ (isOpen_awayStrips _ _ _)).measurableSet.preimage measurable_snd)]
    have he : ((F.system.timeWindow J.val).vertices.filter fun v =>
        label F (physical E o r) (F.point v)∈Prod.snd ⁻¹' (encode '' awayStrips (ti J) (theta J) (c J))) =
      ((S.window (s J) (m J) (hsm J)).vertices.filter fun v => pnt v∈awayStrips (ti J) (theta J) (c J)) := by
      rw [show (S.window (s J) (m J) (hsm J)).vertices=(F.system.timeWindow J.val).vertices from
        F.system.relative_vertices J.property]
      apply Finset.filter_congr
      intro v _
      exact encode_injective.mem_set_image
    rw [he]
    apply (div_le_iff₀ hpos).mpr
    have hh : (((S.window (s J) (m J) (hsm J)).vertices.filter fun v => pnt v∈awayStrips (ti J) (theta J) (c J)).card:ℝ) ≤
        2*∑ i∈batchRange _ (s J) (m J), w i := by
      rw [sum_batchRange (hsm J)]
      dsimp only [w]
      exact_mod_cast hfinite J
    calc
      _ ≤ 2*∑ i∈batchRange _ (s J) (m J), w i := hh
      _ = 2*b J*(F.n:ℝ) := by
        dsimp [b]
        field_simp
  · intro D hD
    have hd : Set.PairwiseDisjoint (↑D : Set (Subwindow K)) (fun J => batchRange (length F.R K) (s J) (m J)) := by
      intro J hJ H hH hJH
      exact relative_range_disjoint F.R J H (hD hJ hH hJH)
    constructor
    · change (∑ J∈D, b J) ≤ 4
      simp only [b,← Finset.sum_div]
      apply (div_le_iff₀ hpos).mpr
      exact (sum_disjoint_ranges D s m hd w hw).trans hcost
    · change (∑ J∈D, theta J) ≤ 1
      have he (J : Subwindow K) : theta J=∑ i∈batchRange _ (s J) (m J), (t i.succ-t i.castSucc) :=
        (parameter_range_sum (hsm J) t).symm
      simp_rw [he]
      exact parameter_budget D s m hd t ht htI

end PlanarHalving.Boundary

namespace PlanarHalving.RankLimits
open Set TimeWindows Boundary
open scoped Classical

lemma localPartition_subset {K J : Window} {m : ℕ} (h : J∈localPartition K m) : carrier J⊆carrier K :=
  (Finset.mem_filter.mp h).2

noncomputable def subPartition (K : Window) (m : ℕ) : Finset (Subwindow K) :=
  (localPartition K m).attach.image (fun J => (⟨J.val,localPartition_subset J.property⟩ : Subwindow K))

lemma mem_subPartition {K : Window} {m : ℕ} {J : Subwindow K} :
    J∈subPartition K m ↔ J.val∈localPartition K m := by
  unfold subPartition
  constructor
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact j.property
  · intro h
    exact Finset.mem_image.mpr ⟨⟨J.val,h⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩

lemma subPartition_map_val (K : Window) (m : ℕ) :
    (subPartition K m).image Subtype.val=localPartition K m := by
  ext J
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact mem_subPartition.mp hj
  · intro h
    exact Finset.mem_image.mpr ⟨⟨J,localPartition_subset h⟩,mem_subPartition.mpr h,rfl⟩

lemma subPartition_sum {M : Type*} [AddCommMonoid M] (K : Window) (m : ℕ) (f : Window → M) :
    ∑ J∈subPartition K m, f J.val=∑ J∈localPartition K m, f J := by
  rw [← subPartition_map_val K m]
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]

lemma subPartition_disjoint (K : Window) (m : ℕ) :
    Set.PairwiseDisjoint (↑(subPartition K m):Set (Subwindow K)) (fun J => carrier J.val) := by
  intro J hJ H hH hJH
  exact localPartition_disjoint K m (mem_subPartition.mp hJ) (mem_subPartition.mp hH)
    (fun he => hJH (Subtype.ext he))

lemma subPartition_card (K : Window) (m : ℕ) : (subPartition K m).card ≤ 2^(K.1+m) := by
  have he : (subPartition K m).card=(localPartition K m).card := by
    rw [← subPartition_map_val K m,Finset.card_image_of_injective _ Subtype.val_injective]
  rw [he]
  apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
  exact (Finset.card_image_le).trans (by simp)

lemma subPartition_tail {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (K : Window) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    (((subPartition K m).filter fun J => u < ((L.vertices J.val).mass:ℝ)).card:ℝ) ≤
      10000*u^(-(4:ℝ)/3) := by
  have hh := h.activity_tail E (K.1+m) hu
  rw [← filter_timePartition (K.1+m) (fun J => u < ((L.vertices J).mass:ℝ))] at hh
  apply hh.trans'
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro J hJ
    obtain ⟨hJ,hJu⟩ := Finset.mem_filter.mp hJ
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (mem_subPartition.mp hJ)).1,hJu⟩
  · exact Subtype.val_injective.injOn

end PlanarHalving.RankLimits

namespace PlanarHalving.Enhancement
open Set Filter MeasureTheory Batches TimeWindows RankLimits Limits Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma limit_vertices_le {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i))) (J : Window) :
    (M (.vertex J) : Measure Space) ≤ (M .point : Measure Space) :=
  measure_le_of_weak_limits (hM (.vertex J)) (hM .point) (fun n => vertices_le_points (F n) (ψ n) J)

lemma limit_edge_ac {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i)))
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) : (M (.edge J) : Measure Space) ≪ (M .point : Measure Space) := by
  apply Measure.AbsolutelyContinuous.trans (μ₂ := (M (.vertex J) : Measure Space))
    _ (Measure.absolutelyContinuous_of_le (limit_vertices_le hM J))
  intro U hU
  let V := toMeasurable (M (.vertex J) : Measure Space) U
  have hc := local_cubic hM hC hcoeff herror J (measurableSet_toMeasurable (M (.vertex J) : Measure Space) U)
  have hV : M (.vertex J) V=0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,measure_toMeasurable]
    exact hU
  change (M (.edge J) V:ℝ)^3 ≤ C*((M (.vertex J)).mass:ℝ)^3*(M (.vertex J) V:ℝ) at hc
  rw [hV,NNReal.coe_zero,mul_zero] at hc
  have hz : M (.edge J) V=0 := by
    apply NNReal.coe_injective
    exact (pow_eq_zero_iff (by norm_num : (3:ℕ)≠0)).mp
      (le_antisymm hc (pow_nonneg (NNReal.coe_nonneg _) _))
  apply measure_mono_null (subset_toMeasurable _ _)
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz,ENNReal.coe_zero]

lemma lifted_mass (μ ν : FiniteMeasure Space) (ρ : FiniteMeasure Labels)
    (hac : (ν : Measure Space) ≪ (μ : Measure Space)) (hmap : ν.map Prod.fst=ρ)
    {G : Set Labels} (hG : MeasurableSet G) :
    (ν (Prod.fst ⁻¹' G ∩ (μ : Measure Space).support):ℝ)=(ρ G:ℝ) := by
  have hr := congrArg (fun m : Measure Space => m univ)
    (support_lift_restrict (μ:Measure Space) (ν:Measure Space) hac (Prod.fst ⁻¹' G))
  simp only [Measure.restrict_apply_univ] at hr
  have he := congrArg (fun m : FiniteMeasure Labels => (m:Measure Labels) G) hmap
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hG] at he
  change ((ν:Measure Space) _).toReal=((ρ:Measure Labels) G).toReal
  rw [hr,he]

lemma projected_mass (ν : FiniteMeasure Space) (ρ : FiniteMeasure Labels)
    (hmap : ν.map Prod.fst=ρ) : ν.mass=ρ.mass := by
  rw [← hmap]
  change ν univ=(ν.map Prod.fst) univ
  rw [FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,preimage_univ]

end PlanarHalving.Enhancement

namespace PlanarHalving.Boundary
open Set Filter Metric MeasureTheory Batches TimeWindows RankLimits Enhancement Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma enhanced_boundary_zero {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (emb : ∀ n, (F n).SweepEmbedding)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (K : Window) (E : ℕ → Point ≃L[ℝ] Point) (o : ℕ → Point) (r : ℕ → ℝ)
    (hr : ∀ n, 0<r n)
    (hframe : ∀ n, ∃ A B l u : ℝ, 0<A ∧ 0<B ∧ l<u ∧
      E n (1,0)=A • (1,l) ∧ E n (0,1)=B • (1,u) ∧
      ∀ i, ((F n).system.timeWindow K).slope i∈Icc l u)
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (physical (E n) (o n) (r n)) i) atTop (𝓝 (M i)))
    (hprojection : ∀ i, (M i).map Prod.fst=old L i)
    (G : Set Labels) (hG : MeasurableSet G)
    (hpos : ∀ z∈Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support,
      ‖decode z.2‖≤1 ∧ encode (decode z.2)=z.2)
    {D : ℝ} (hD : 0≤D)
    (hdisk : ∀ x : Point, ∀ t : ℝ, 0<t →
      (((M .point : Measure Space).restrict (Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support)).map
        (decode ∘ Prod.snd)) (closedBall x t)≤ENNReal.ofReal (D*t^((32:ℝ)/17))) :
    (L.edgeWindow K G:ℝ)=0 := by
  classical
  let H := Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support
  have hH : MeasurableSet H := (hG.preimage measurable_fst).inter (M .point : Measure Space).isClosed_support.measurableSet
  choose A B lo up ha hb hlu h1 h2 hspan using hframe
  have hparams := fun n => finite_window_params (F n) K (E n)
    (ha n) (hb n) (hlu n) (h1 n) (h2 n) (hspan n) (o n) (hr n)
  choose p hp hbudget using hparams
  obtain ⟨φ,b,t,θ,c,hφ,hbounds,hb,ht,hθ,hc⟩ := params_subsequence p
  have haway (J : Subwindow K) :
      (M (.vertex J.val) (Prod.snd ⁻¹' (encode '' awayStrips (t J) (θ J) (c J))):ℝ)≤2*b J := by
    apply moving_strips_limit ((hM (.vertex J.val)).comp hφ.tendsto_atTop)
      (ht J) (hθ J) (hc J) (hb J)
    exact Filter.Eventually.of_forall (fun n => hp (φ n) J)
  have hactivity (J : Subwindow K) : (M (.vertex J.val) H:ℝ)≤
      2*b J+3*(13*D*(1+3^((32:ℝ)/17))*36^((32:ℝ)/17-1))*θ J^((32:ℝ)/17-1) := by
    exact limiting_activity_bound (M .point) (M (.vertex J.val)) H hH
      (limit_vertices_le hM J.val) hpos hD (by norm_num) (hbounds J).2.2.1.1
      (hbounds J).1.1 (c J) hdisk (haway J)
  have hbudgets (m : ℕ) : (∑ J∈subPartition K m, b J)≤4 ∧ (∑ J∈subPartition K m, θ J)≤1 := by
    constructor
    · exact finite_budget_limit (subPartition K m) _ b hb
        (Filter.Eventually.of_forall (fun n => (hbudget (φ n) (subPartition K m) (subPartition_disjoint K m)).1))
    · exact finite_budget_limit (subPartition K m) _ θ hθ
        (Filter.Eventually.of_forall (fun n => (hbudget (φ n) (subPartition K m) (subPartition_disjoint K m)).2))
  have hlam (J : Window) : (M (.edge J) H:ℝ)=(L.edgeWindow J G:ℝ) :=
    lifted_mass (M .point) (M (.edge J)) (L.edgeWindow J)
      (limit_edge_ac hM hC hcoeff herror J) (hprojection (.edge J)) hG
  have hvertex (J : Window) : (M (.vertex J)).mass=(L.vertices J).mass :=
    projected_mass _ _ (hprojection (.vertex J))
  let q : ℕ → ℝ := fun m => (2:ℝ)^(K.1+m)
  have hq : ∀ m, 0<q m := fun _ => by positivity
  have hqtop : Tendsto q atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp (tendsto_atTop_mono (fun n => Nat.le_add_left n K.1) tendsto_id)
  apply mass_eq_zero (subPartition K) (fun _ J => (M (.edge J.val) H:ℝ))
    (fun _ J => (M (.vertex J.val) H:ℝ)) (fun _ J => ((L.vertices J.val).mass:ℝ))
    (fun _ J => b J) (fun _ J => θ J) q (A:=C)
    (H:=10000) (B:=3*(13*D*(1+3^((32:ℝ)/17))*36^((32:ℝ)/17-1))) (B₀:=4) (T:=1)
    (α:=(32:ℝ)/17-1) (NNReal.coe_nonneg _) hC (by positivity) (by norm_num)
    (by norm_num) (by norm_num) hq hqtop
  · intro m
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using
      (Nat.cast_le (α:=ℝ).mpr (subPartition_card K m))
  · intro m J _
    exact NNReal.coe_nonneg _
  · intro m J hJ
    rw [hlam]
    have hd := mem_timePartition.mp (Finset.mem_filter.mp (mem_subPartition.mp hJ)).1
    apply (NNReal.coe_le_coe.mpr ((L.edgeWindow J.val).apply_le_mass G)).trans_eq
    rw [hF.edgeWindow_mass hR,hd]
    simp only [q,Nat.cast_pow,Nat.cast_ofNat]
  · intro m J _; exact NNReal.coe_nonneg _
  · intro m J _; exact NNReal.coe_nonneg _
  · intro m J _; exact (hbounds J).2.2.1.1
  · intro m J _
    have hh := Enhancement.local_cubic hM hC hcoeff herror J.val hH
    rwa [hvertex] at hh
  · intro m J _; exact hactivity J
  · intro m; exact (hbudgets m).1
  · intro m; exact (hbudgets m).2
  · intro m u hu; exact subPartition_tail hF emb K m hu
  · intro m
    simp_rw [hlam]
    rw [subPartition_sum K m (fun J => (L.edgeWindow J G:ℝ)),hF.localPartition_sum hR K m hG]

end PlanarHalving.Boundary

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

lemma Converges.window_le_edge {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeWindow J : Measure Labels)≤(L.edge : Measure Labels) := by
  rw [Data.edgeWindow,Data.edge,FiniteMeasure.toMeasure_map,FiniteMeasure.toMeasure_map,
    h.restriction_eq hR]
  exact Measure.map_mono Measure.restrict_le_self measurable_fst

noncomputable def commonSet (L : Data) {K : Window} (q : CommonChoice K) : Set Labels :=
  {z | L.conditional z (carrier q.val.1)≠0 ∧ L.conditional z (carrier q.val.2.1)≠0 ∧
    L.conditional z (carrier q.val.2.2)≠0}

lemma commonSet_measurable (L : Data) {K : Window} (q : CommonChoice K) :
    MeasurableSet (commonSet L q) := by
  have hm (J : Window) : MeasurableSet {z | L.conditional z (carrier J)≠0} :=
    ((L.conditional.measurable_coe (measurable_carrier J)) (measurableSet_singleton 0)).compl
  exact (hm q.val.1).inter ((hm q.val.2.1).inter (hm q.val.2.2))

lemma Converges.common_positive {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (K : Window)
    (hna : ∀ᵐ z ∂(L.edge : Measure Labels), NullSingletonClass (L.conditional z))
    {T : Set Labels} (hT : MeasurableSet T) (hTp : (L.edge : Measure Labels) T≠0)
    (hK : ∀ z∈T, L.conditional z (carrier K)≠0) :
    ∃ (q : CommonChoice K) (E : Set Labels), MeasurableSet E ∧ E⊆T ∧
      (∀ z∈E, z∈commonSet L q) ∧ (L.edgeWindow q.val.2.2 : Measure Labels) E≠0 ∧
      (L.edgeWindow q.val.2.2 : Measure Labels).restrict E ≤ (L.edge : Measure Labels).restrict T := by
  have hcover : ∀ᵐ z ∂(L.edge : Measure Labels).restrict T, ∃ q : CommonChoice K, z∈commonSet L q := by
    filter_upwards [ae_restrict_of_ae hna,ae_restrict_mem hT] with z hz hzt
    let := hz
    exact exists_commonChoice (L.conditional z) K (hK z hzt)
  obtain ⟨q,hq⟩ := positive_countable_selection (L.edge : Measure Labels) T hT hTp (commonSet L) hcover
  let E := T∩commonSet L q
  have hE : MeasurableSet E := hT.inter (commonSet_measurable L q)
  have hac : (L.edge : Measure Labels).restrict E ≪ (L.edgeWindow q.val.2.2 : Measure Labels) := by
    rw [h.window_withDensity hR]
    exact restrict_ac_withDensity _ _ (L.conditional.measurable_coe (measurable_carrier _)) hE
      (fun z hz => hz.2.2.2)
  refine ⟨q,E,hE,inter_subset_left,fun _ hz => hz.2,?_,?_⟩
  · intro he
    have hzero := hac he
    rw [Measure.restrict_apply hE,inter_self] at hzero
    exact hq hzero
  · exact Measure.restrict_mono inter_subset_left (h.window_le_edge hR _)

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows
open scoped Topology unitInterval ENNReal

lemma coordinate_lines_null (x : ℝ) :
    (volume : Measure Point) {p | p.1=x}=0 ∧ (volume : Measure Point) {p | p.2=x}=0 := by
  have h1 : {p : Point | p.1=x}=({x}:Set ℝ)×ˢuniv := by ext p; simp
  have h2 : {p : Point | p.2=x}=(univ:Set ℝ)×ˢ{x} := by ext p; simp
  rw [h1,h2,Measure.volume_eq_prod,Measure.prod_prod,Measure.prod_prod]
  simp

lemma pairCoordinates_interior_ae {ν : Measure Labels} {A B : Window}
    (hproj : ν.map (pairCoordinates true A B) ≪ volume) :
    ∀ᵐ z ∂ν, pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  have hq : Measure.QuasiMeasurePreserving (pairCoordinates true A B) ν volume :=
    ⟨(continuous_pairCoordinates true A B).measurable,hproj⟩
  have ha (x : ℝ) : ∀ᵐ p ∂(volume : Measure Point), p.1≠x := by
    simpa only [ae_iff,not_not] using (coordinate_lines_null x).1
  have hb (x : ℝ) : ∀ᵐ p ∂(volume : Measure Point), p.2≠x := by
    simpa only [ae_iff,not_not] using (coordinate_lines_null x).2
  filter_upwards [hq.ae (ha 0),hq.ae (ha 1),hq.ae (hb (-1)),hq.ae (hb 0)] with z h1 h2 h3 h4
  dsimp [pairCoordinates,signedPair] at h1 h2 h3 h4 ⊢
  have hzA := (z A).property
  have hzB := (z B).property
  exact ⟨⟨lt_of_le_of_ne hzA.1 (Ne.symm h1),lt_of_le_of_ne hzA.2 h2⟩,
    ⟨lt_of_le_of_ne (by linarith [hzB.2]) (Ne.symm h3),lt_of_le_of_ne (by linarith [hzB.1]) h4⟩⟩

end PlanarHalving.RankLimits

end OAI
