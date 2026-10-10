import OAI.Combinatorics.HalvingLines.Labels

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

inductive MeasureIndex where
  | point
  | vertices (J : Window)
  | time
  | restrict (J : Window)
  | cross (A B : Window)
  deriving Countable

abbrev LimitSpace : MeasureIndex → Type
  | .point => Labels
  | .vertices _ => Labels
  | .time => Labels × I
  | .restrict _ => Labels × I
  | .cross _ _ => Labels

noncomputable instance (i : MeasureIndex) : MetricSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (MetricSpace _)
instance (i : MeasureIndex) : CompactSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (CompactSpace _)
instance (i : MeasureIndex) : Nonempty (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (Nonempty _)
noncomputable instance (i : MeasureIndex) : MeasurableSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (MeasurableSpace _)
instance (i : MeasureIndex) : BorelSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (BorelSpace _)

noncomputable def Configuration.measures (F : Configuration) : ∀ i, FiniteMeasure (LimitSpace i)
  | .point => F.points
  | .vertices J => F.vertices J
  | .time => F.edgeTime
  | .restrict J => F.timeRestrict J
  | .cross A B => F.crossings A B

lemma Configuration.measures_mass_le (F : Configuration) (i : MeasureIndex) :
    (F.measures i).mass ≤ 2 := by
  cases i with
  | point => exact F.points_mass.le.trans (by norm_num)
  | vertices J => exact (F.vertices_mass_le J).trans (by norm_num)
  | time => exact F.edgeTime_mass.le.trans (by norm_num)
  | restrict J => exact (F.timeRestrict_mass_le J).trans (by norm_num)
  | cross A B => exact F.crossings_mass_le A B

structure Data where
  points : FiniteMeasure Labels
  vertices : Window → FiniteMeasure Labels
  edgeTime : FiniteMeasure (Labels × I)
  timeRestrict : Window → FiniteMeasure (Labels × I)
  crossings : Window → Window → FiniteMeasure Labels

noncomputable def Data.ofFamily (f : ∀ i, FiniteMeasure (LimitSpace i)) : Data where
  points := f .point
  vertices := fun J => f (.vertices J)
  edgeTime := f .time
  timeRestrict := fun J => f (.restrict J)
  crossings := fun A B => f (.cross A B)

structure Converges (F : ℕ → Configuration) (L : Data) : Prop where
  points : Tendsto (fun n => (F n).points) atTop (𝓝 L.points)
  vertices : ∀ J, Tendsto (fun n => (F n).vertices J) atTop (𝓝 (L.vertices J))
  edgeTime : Tendsto (fun n => (F n).edgeTime) atTop (𝓝 L.edgeTime)
  timeRestrict : ∀ J, Tendsto (fun n => (F n).timeRestrict J) atTop (𝓝 (L.timeRestrict J))
  crossings : ∀ A B, Tendsto (fun n => (F n).crossings A B) atTop (𝓝 (L.crossings A B))

theorem subsequence (F : ℕ → Configuration) :
    ∃ (φ : ℕ → ℕ) (L : Data), StrictMono φ ∧ Converges (F ∘ φ) L := by
  obtain ⟨φ,f,hφ,hf⟩ := finiteMeasure_subsequence_dependent
    (fun n => (F n).measures) (fun _ => 2) (fun n i => (F n).measures_mass_le i)
  exact ⟨φ,Data.ofFamily f,hφ,⟨hf .point,fun J => hf (.vertices J),hf .time,
    fun J => hf (.restrict J),fun A B => hf (.cross A B)⟩⟩

lemma Converges.points_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L) :
    L.points.mass=1 := by
  have hh := FiniteMeasure.continuous_mass.tendsto L.points |>.comp h.points
  exact tendsto_nhds_unique hh (by simpa only [Function.comp_def,Configuration.points_mass] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0)) atTop (𝓝 1)))
lemma Converges.edgeTime_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L) :
    L.edgeTime.mass=1 := by
  have hh := FiniteMeasure.continuous_mass.tendsto L.edgeTime |>.comp h.edgeTime
  exact tendsto_nhds_unique hh (by simpa only [Function.comp_def,Configuration.edgeTime_mass] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0)) atTop (𝓝 1)))

lemma Converges.time_marginal {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) :
    L.edgeTime.map Prod.snd=⟨volume,inferInstance⟩ := by
  have hm := (FiniteMeasure.continuous_map continuous_snd).tendsto L.edgeTime |>.comp h.edgeTime
  have ht := timeMeasure_tendsto (fun n => (F n).R) hR
  apply tendsto_nhds_unique hm
  convert ht using 1
  funext n
  exact (F n).system.labelTimeMeasure_time _

end PlanarHalving.RankLimits
namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter Limits
open scoped Topology NNReal ENNReal unitInterval

lemma normalized_perturbed_fintype_sum_le {m : ℕ} [NeZero m] {α : Type*} [Fintype α]
    (slots : α → Fin m × Fin m) (hs : Function.Injective slots)
    (x : α → I × I) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ i, f (x i) ≤ f (gridPoint m (slots i)) + ε) :
    (∑ i, f (x i))/(m : ℝ)^2 ≤
      (∑ j : Fin m × Fin m, f (gridPoint m j))/(m : ℝ)^2 + ε := by
  let e := (Fintype.equivFin α).symm
  have hh := normalized_perturbed_sum_le (slots ∘ e) (hs.comp e.injective)
    (x ∘ e) f hf hε (fun i => hclose (e i))
  have he : (∑ i, f (x (e i)))=∑ i, f (x i) := Equiv.sum_comp e (fun i => f (x i))
  simpa only [Function.comp_apply,he] using hh

lemma perturbed_fintype_grid_limit (m : ℕ → ℕ) [∀ n, NeZero (m n)]
    (hm : Tendsto m atTop atTop) {α : ℕ → Type*} [∀ n, Fintype (α n)]
    (x : ∀ n, α n → I × I) (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hslots : ∀ᶠ n in atTop, ∃ slots : α n → Fin (m n) × Fin (m n),
      Function.Injective slots ∧ ∀ i, dist (x n i) (gridPoint (m n) (slots i)) ≤ d n)
    (μ : FiniteMeasure (I × I))
    (hμ : Tendsto (fun n => weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n)) atTop (𝓝 μ)) :
    (μ : Measure (I × I)) ≤ volume := by
  let ν : FiniteMeasure (I × I) := ⟨volume,inferInstance⟩
  apply measure_le_of_test μ ν
  intro f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hdδ : ∀ᶠ n in atTop, d n < δ := (tendsto_order.mp hd).2 δ hδ
  have hineq : ∀ᶠ n in atTop,
      ∫ t, f t ∂(weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n) : Measure (I × I)) ≤
        (∑ j : Fin (m n) × Fin (m n), f (gridPoint (m n) j))/(m n : ℝ)^2 + ε := by
    filter_upwards [hdδ,hslots] with n hn hs
    obtain ⟨slots,hs,hclose⟩ := hs
    rw [integral_weightedAtoms]
    simp only [NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast]
    rw [← div_eq_inv_mul]
    apply normalized_perturbed_fintype_sum_le slots hs (x n) f hf hε.le
    intro i
    have h := hfδ ((hclose i).trans_lt hn)
    rw [Real.dist_eq,abs_lt] at h
    linarith [h.2]
  have hlim := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  have hgrid := (riemann_tendsto m hm f).add_const ε
  exact le_of_tendsto_of_tendsto hlim hgrid hineq

end PlanarHalving.UniformPartition
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.crossing_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Before A B) :
    ((L.crossings A B).map (fun z => (z A,z B)) : Measure (I × I)) ≤ volume := by
  let m := fun n => (F n).a*(F n).n
  let x := fun n w => ((F n).label ((F n).system.windowCrossPoint A B w) A,
    (F n).label ((F n).system.windowCrossPoint A B w) B)
  have hd : Tendsto (fun n => 2/(m n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hM)
  have hs : ∀ᶠ n in atTop, ∃ slots : _ → Fin (m n) × Fin (m n),
      Function.Injective slots ∧ ∀ w, dist (x n w) (UniformPartition.gridPoint (m n) (slots w)) ≤ 2/(m n : ℝ) := by
    filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B] with n hA hB
    exact (F n).system.window_crossing_slots (F n).generic hAB hA hB
  apply UniformPartition.perturbed_fintype_grid_limit m hM x _ hd hs
  have hc : Continuous (fun z : Labels => (z A,z B)) :=
    (continuous_apply A).prodMk (continuous_apply B)
  have hh := (FiniteMeasure.continuous_map hc).tendsto (L.crossings A B) |>.comp (h.crossings A B)
  convert hh using 1
  funext n
  exact (map_weightedAtoms _ _ hc.measurable).symm

end PlanarHalving.RankLimits
namespace PlanarHalving.UniformPartition
open MeasureTheory Set
open scoped unitInterval

lemma volume_frontier_cell (m : ℕ) [NeZero m] (i : Fin m) :
    volume (frontier (cell m i))=0 := by
  let a := boundary m i.castSucc
  let b := boundary m i.succ
  have hab : (a : ℝ)<(b : ℝ) := by
    apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr (NeZero.pos m))
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    linarith
  have hpair : (Subtype.val : I → ℝ) ⁻¹' {(a : ℝ),(b : ℝ)}={a,b} := by
    ext t
    simp only [mem_preimage,mem_insert_iff,mem_singleton_iff,Subtype.coe_inj]
  unfold cell
  split_ifs
  · change volume (frontier ((Subtype.val : I → ℝ) ⁻¹' Icc (a : ℝ) (b : ℝ)))=0
    apply measure_mono_null (continuous_subtype_val.frontier_preimage_subset _)
    rw [frontier_Icc hab.le,hpair]
    exact Set.Finite.measure_zero ((Set.finite_singleton b).insert a) _
  · change volume (frontier ((Subtype.val : I → ℝ) ⁻¹' Ico (a : ℝ) (b : ℝ)))=0
    apply measure_mono_null (continuous_subtype_val.frontier_preimage_subset _)
    rw [frontier_Ico hab,hpair]
    exact Set.Finite.measure_zero ((Set.finite_singleton b).insert a) _

end PlanarHalving.UniformPartition
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.null_time_boundary {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeTime : Measure (Labels×I)) (frontier (Prod.snd ⁻¹' carrier J))=0 := by
  apply measure_mono_null (continuous_snd.frontier_preimage_subset _)
  rw [← Measure.map_apply measurable_snd isClosed_frontier.measurableSet]
  have he : (Measure.map Prod.snd (L.edgeTime : Measure (Labels×I)))=volume :=
    congrArg (fun m : FiniteMeasure I => (m : Measure I)) (h.time_marginal hR)
  rw [he]
  exact UniformPartition.volume_frontier_cell _ _

lemma Converges.restriction_eq {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.timeRestrict J : Measure (Labels×I))=(L.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J) :=
  restriction_limit_eq h.edgeTime (h.timeRestrict J)
    ((measurable_carrier J).preimage measurable_snd) (h.null_time_boundary hR J) (fun _ => rfl)

noncomputable def Data.edge (L : Data) : FiniteMeasure Labels := L.edgeTime.map Prod.fst
noncomputable def Data.edgeWindow (L : Data) (J : Window) : FiniteMeasure Labels :=
  (L.timeRestrict J).map Prod.fst

lemma Converges.restriction_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    ((L.timeRestrict J).mass : ℝ≥0∞)=(2^J.1 : ℝ≥0∞)⁻¹ := by
  rw [FiniteMeasure.ennreal_mass,h.restriction_eq hR,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  rw [← Measure.map_apply measurable_snd (measurable_carrier J)]
  have he : (Measure.map Prod.snd (L.edgeTime : Measure (Labels×I)))=volume :=
    congrArg (fun m : FiniteMeasure I => (m : Measure I)) (h.time_marginal hR)
  rw [he]
  rw [TimeWindows.carrier,UniformPartition.cell_volume]
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,one_div]
  norm_cast

end PlanarHalving.RankLimits
namespace PlanarHalving.Batches
open MeasureTheory Set Limits TimeWindows
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.window_endpoint_eq (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Fin n → X) (J : Window) :
    ((S.labelTimeMeasure z).restrict (Prod.snd ⁻¹' carrier J)).map Prod.fst=
      (S.timeWindow J).endpointMeasure z ((R : ℝ≥0)*(a : ℝ≥0)^2) := by
  classical
  apply FiniteMeasure.eq_of_forall_toMeasure_apply_eq
  intro U hU
  have he : ((((S.labelTimeMeasure z).restrict (Prod.snd ⁻¹' carrier J)).map Prod.fst) U : ℝ)=
      ((S.timeWindow J).endpointMeasure z ((R : ℝ≥0)*(a : ℝ≥0)^2) U : ℝ) := by
    rw [FiniteMeasure.map_apply _ measurable_fst hU,
      FiniteMeasure.restrict_apply _ _ (hU.preimage measurable_fst),
      System.labelTimeMeasure,weightedAtoms_apply_finset _ _
        ((hU.preimage measurable_fst).inter ((measurable_carrier J).preimage measurable_snd)),
      System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
    congr 2
    apply Finset.card_bij (fun e he =>
      (⟨e.val,(S.timeWindow_mem J e).mpr (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_inter_iff,Set.mem_preimage] at he
        exact he.2)⟩ : ↥(S.timeWindow J).edges))
    · intro e he
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,
        Set.mem_inter_iff,Set.mem_preimage] at he ⊢
      exact he.1
    · intro e _ f _ hef
      exact Subtype.ext (congrArg (fun x : ↥(S.timeWindow J).edges => x.val) hef)
    · intro e he
      let f : ↥S.edges := ⟨e.val,S.timeWindow_edges J e.property⟩
      refine ⟨f,?_,rfl⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,
        Set.mem_inter_iff,Set.mem_preimage] at he ⊢
      exact ⟨he,(S.timeWindow_mem J f).mp e.property⟩
  have he' := NNReal.coe_injective he
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) he'

lemma System.vertexMass_ratio (S : @System n R k a P) (z : Fin n → Point) :
    ((S.vertexMeasure z).mass : ℝ)=(S.vertices.card : ℝ)/(n : ℝ) := by
  rw [System.vertexMeasure,mass_weightedAtoms,Fintype.card_coe]
  simp only [NNReal.coe_mul,NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def Configuration.edgeWindow (F : Configuration) (J : Window) : FiniteMeasure Labels :=
  (F.timeRestrict J).map Prod.fst

lemma Configuration.edgeWindow_eq (F : Configuration) (J : Window) :
    F.edgeWindow J=(F.system.timeWindow J).endpointMeasure (F.label ∘ F.point)
      ((F.R : ℝ≥0)*(F.a : ℝ≥0)^2) := F.system.window_endpoint_eq _ J

lemma Configuration.vertices_mass_ratio (F : Configuration) (J : Window) :
    ((F.vertices J).mass : ℝ)=((F.system.timeWindow J).vertices.card : ℝ)/(F.n : ℝ) := by
  rw [Configuration.vertices,System.vertexMeasure,mass_weightedAtoms,Fintype.card_coe]
  simp only [NNReal.coe_mul,NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]

lemma Configuration.window_cubed_bound (F : Configuration) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (F.edgeWindow J U : ℝ)^3 ≤
      (4608 * (F.a : ℝ)^2 * F.n^4 / ((F.R : ℝ)*F.a^2)^3) *
        ((F.vertices J).mass : ℝ)^3 * (F.vertices J U : ℝ) +
      13824 * ((F.system.timeWindow J).vertices.card : ℝ)^3 / ((F.R : ℝ)*F.a^2)^3 := by
  rw [F.edgeWindow_eq,F.vertices_mass_ratio]
  have hR : 0 < (F.R : ℝ≥0) := Nat.cast_pos.mpr F.R_pos
  have ha : 0 < (F.a : ℝ≥0) := Nat.cast_pos.mpr F.a_pos
  exact (F.system.timeWindow J).atomic_cubed_bound F.generic _ (by positivity) hU

end PlanarHalving.RankLimits
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.rankGraphs (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    (S.timeWindow J).FullGraphs (S.drawing.exteriorCrossings (S.timeWindow J).edges) :=
  (S.rankFamily_spec hP J hJ).choose

lemma System.rankGraphs_eq (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    (S.rankGraphs hP J hJ).graph=(S.rankFamily hP J).graph :=
  (S.rankFamily_spec hP J hJ).choose_spec.1.symm

noncomputable def System.rankCoordinate (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    Coordinate (S.rankGraphs hP J hJ).lower (S.rankGraphs hP J hJ).upper :=
  smoothedCoordinate (Nat.mul_pos (NeZero.pos a) (NeZero.pos n))
    (S.rankGraphs hP J hJ).graph (S.rankFamily hP J).scale_pos
    (S.rankGraphs hP J hJ).continuous (S.rankGraphs hP J hJ).slopes

lemma System.rankCoordinate_value (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) (p : Point) :
    (S.rankCoordinate hP J hJ).value p=(S.labels hP p J : ℝ) := by
  change smoothed (S.rankGraphs hP J hJ).graph _ p=smoothed (S.rankFamily hP J).graph _ p
  rw [S.rankGraphs_eq]

noncomputable def System.rankHomeomorph (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) : Point ≃ₜ (UnitOpen × UnitOpen) :=
  pairHomeomorph (S.rankCoordinate hP A hA) (S.rankCoordinate hP B hB)
    (S.timeWindow_graph_gap hAB _ _)

lemma System.rankHomeomorph_coordinates (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (p : Point) :
    (((S.rankHomeomorph hP hAB hA hB) p).1 : ℝ)=(S.labels hP p A : ℝ) ∧
    (((S.rankHomeomorph hP hAB hA hB) p).2 : ℝ)=(S.labels hP p B : ℝ) :=
  ⟨S.rankCoordinate_value hP A hA p,S.rankCoordinate_value hP B hB p⟩

noncomputable def System.rankInCoordinates (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (C : Window) : UnitOpen × UnitOpen → ℝ :=
  fun p => (S.labels hP ((S.rankHomeomorph hP hAB hA hB).symm p) C : ℝ)

lemma System.rankInCoordinates_eq (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (C : Window) (hC : 0 < length R C) :
    S.rankInCoordinates hP hAB hA hB C=
      inCoordinates (S.rankCoordinate hP A hA) (S.rankCoordinate hP B hB)
        (S.timeWindow_graph_gap hAB _ _) (S.rankCoordinate hP C hC) := by
  funext p
  exact (S.rankCoordinate_value hP C hC _).symm

lemma System.rankInCoordinates_before (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hCA : Before C A) (hCB : Before C B)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Monotone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Antitone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_monotone_left _ _ _ _ (S.timeWindow_graph_gap hCB _ _) v,
    fun u => inCoordinates_antitone_right _ _ _ _ (S.timeWindow_graph_gap hCA _ _) u⟩

lemma System.rankInCoordinates_between (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hAC : Before A C) (hCB : Before C B)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Monotone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Monotone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_monotone_left _ _ _ _ (S.timeWindow_graph_gap hCB _ _) v,
    fun u => inCoordinates_monotone_right _ _ _ _ (S.timeWindow_graph_gap hAC _ _) u⟩

lemma System.rankInCoordinates_after (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hAC : Before A C) (hBC : Before B C)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Antitone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Monotone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_antitone_left _ _ _ _ (S.timeWindow_graph_gap hBC _ _) v,
    fun u => inCoordinates_monotone_right _ _ _ _ (S.timeWindow_graph_gap hAC _ _) u⟩

end PlanarHalving.Batches
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

lemma measure_le_of_weak_limits {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ ν : FiniteMeasure X} {μs νs : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (h : ∀ n, (μs n : Measure X) ≤ (νs n : Measure X)) :
    (μ : Measure X) ≤ (ν : Measure X) := by
  apply measure_le_of_test
  intro f hf
  exact le_of_tendsto_of_tendsto
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f)
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
    (Eventually.of_forall (fun n => integral_mono_measure (h n)
      (Eventually.of_forall hf) (BoundedContinuousFunction.integrable (νs n : Measure X) f)))

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.vertices_le_points (F : Configuration) (J : Window) :
    (F.vertices J : Measure Labels) ≤ (F.points : Measure Labels) := by
  classical
  apply Measure.le_iff.mpr
  intro U hU
  have he : (F.vertices J U : ℝ) ≤ (F.points U : ℝ) := by
    rw [Configuration.vertices,System.vertexMeasure_apply _ _ hU,
      Configuration.points,weightedAtoms_apply_finset _ _ hU]
    simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp he))

lemma Converges.vertices_le_points {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (J : Window) : (L.vertices J : Measure Labels) ≤ (L.points : Measure Labels) :=
  measure_le_of_weak_limits (h.vertices J) h.points (fun n => (F n).vertices_le_points J)

lemma Converges.edgeWindow {F : ℕ → Configuration} {L : Data} (h : Converges F L) (J : Window) :
    Tendsto (fun n => (F n).edgeWindow J) atTop (𝓝 (L.edgeWindow J)) :=
  (FiniteMeasure.continuous_map continuous_fst).tendsto _ |>.comp (h.timeRestrict J)

lemma Converges.local_cubic {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4 /
      (((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3 /
      (((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)^3 ≤ C*((L.vertices J).mass : ℝ)^3*(L.vertices J U : ℝ) := by
  have hm : Tendsto (fun n => ((F n).vertices J).mass) atTop (𝓝 ((L.vertices J).mass)) :=
    FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices J)
  have hmR := NNReal.continuous_coe.tendsto _ |>.comp hm
  apply cubed_bound_limit (h.vertices J) (h.edgeWindow J)
    (mul_nonneg hC (pow_nonneg (NNReal.coe_nonneg _) _))
    ((hmR.pow 3).const_mul C) herror
  intro n V hV
  apply ((F n).window_cubed_bound J hV).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (NNReal.coe_nonneg _) _))
      (NNReal.coe_nonneg _)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 3
    exact_mod_cast (show ((F n).system.timeWindow J).vertices.card ≤ (F n).n by
      simpa only [Fintype.card_fin] using ((F n).system.timeWindow J).vertices.card_le_univ)
  exact hU

lemma Converges.window_absolutelyContinuous {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4 /
      (((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3 /
      (((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0)) (J : Window) :
    (L.edgeWindow J : Measure Labels) ≪ (L.points : Measure Labels) := by
  refine (show (L.edgeWindow J : Measure Labels) ≪ (L.vertices J : Measure Labels) from ?_).trans
    (Measure.absolutelyContinuous_of_le (h.vertices_le_points J))
  intro U hU
  have hc := h.local_cubic hC hcoeff herror J (measurableSet_toMeasurable (L.vertices J : Measure Labels) U)
  have hV : ((L.vertices J : Measure Labels) (toMeasurable (L.vertices J : Measure Labels) U))=0 := by
    rwa [measure_toMeasurable]
  have hV' : L.vertices J (toMeasurable (L.vertices J : Measure Labels) U)=0 := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hV
    exact ENNReal.coe_eq_zero.mp hV
  rw [hV',NNReal.coe_zero,mul_zero] at hc
  have hz : L.edgeWindow J (toMeasurable (L.vertices J : Measure Labels) U)=0 := by
    apply NNReal.coe_injective
    change (L.edgeWindow J (toMeasurable (L.vertices J : Measure Labels) U) : ℝ)=0
    exact (pow_eq_zero_iff (by omega : (3:ℕ)≠0)).mp
      (le_antisymm hc (pow_nonneg (NNReal.coe_nonneg _) _))
  apply measure_mono_null (subset_toMeasurable _ _)
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz,ENNReal.coe_zero]

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches Filter
open scoped Topology

lemma Configuration.normalization_coefficient (F : Configuration) {c : ℝ} (hc : 0<c)
    (hnear : c*(F.n : ℝ)^4≤(F.R : ℝ)^3*(F.a : ℝ)^4) :
    4608*(F.a : ℝ)^2*(F.n : ℝ)^4/((F.R : ℝ)*(F.a : ℝ)^2)^3≤4608/c := by
  have ha : (0:ℝ)<F.a := Nat.cast_pos.mpr F.a_pos
  have hR : (0:ℝ)<F.R := Nat.cast_pos.mpr F.R_pos
  apply (div_le_div_iff₀ (pow_pos (mul_pos hR (pow_pos ha _)) _) hc).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnear (by positivity : (0:ℝ)≤4608*(F.a : ℝ)^2)]

lemma Configuration.short_ratio_cube (F : Configuration) {c : ℝ} (hc : 0<c)
    (hnear : c*(F.n : ℝ)^4≤(F.R : ℝ)^3*(F.a : ℝ)^4) :
    ((F.n : ℝ)/((F.R : ℝ)*(F.a : ℝ)))^3≤1/(c*((F.n : ℝ)/(F.a : ℝ))) := by
  have ha : (0:ℝ)<F.a := Nat.cast_pos.mpr F.a_pos
  have hR : (0:ℝ)<F.R := Nat.cast_pos.mpr F.R_pos
  have hn : (0:ℝ)<F.n := Nat.cast_pos.mpr F.n_pos
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (mul_pos hR ha) _) (mul_pos hc (div_pos hn ha))).mpr
  apply (mul_le_mul_iff_left₀ ha).mp
  field_simp
  nlinarith [hnear]

lemma short_ratio_tendsto_zero {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => 1/(c*(((F n).n : ℝ)/(F n).a))) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (hq.const_mul_atTop hc)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hi (ε^3) (pow_pos hε _)
  refine ⟨N,fun n hn => ?_⟩
  have hb := (F n).short_ratio_cube hc (hnear n)
  have hp : (0:ℝ)≤((F n).n : ℝ)/((F n).R*(F n).a) := by positivity
  have hv := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hp]
  exact (pow_lt_pow_iff_left₀ hp hε.le (by omega : (3:ℕ)≠0)).mp (hb.trans_lt hv)

lemma sparse_error_tendsto_zero {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => 13824*((F n).n : ℝ)^3/((F n).R*(F n).a^2)^3) atTop (𝓝 0) := by
  have hsmall := (short_ratio_tendsto_zero hc hnear hq).pow 3 |>.const_mul 13824
  simp only [zero_pow (by omega : (3:ℕ)≠0),mul_zero] at hsmall
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) hsmall
  have ha : (1:ℝ)≤(F n).a := by exact_mod_cast (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  rw [div_pow,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr
  nlinarith

lemma normalization_sizes_atTop {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => (F n).n) atTop atTop ∧
    Tendsto (fun n => (F n).a*(F n).n) atTop atTop ∧
    Tendsto (fun n => (F n).R) atTop atTop := by
  have hn : Tendsto (fun n => ((F n).n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) hq
    exact div_le_self (by positivity) (by exact_mod_cast (F n).a_pos)
  have hn' : Tendsto (fun n => (F n).n) atTop atTop := tendsto_natCast_atTop_iff.mp hn
  refine ⟨hn',tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left _ (F n).a_pos) hn',?_⟩
  apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
  apply tendsto_atTop_mono' atTop ?_ hq
  have hs := (short_ratio_tendsto_zero hc hnear hq).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hs] with n hn
  have ha : (0:ℝ)<(F n).a := Nat.cast_pos.mpr (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  apply (div_le_iff₀ ha).mpr
  have := (div_lt_iff₀ (mul_pos hR ha)).mp hn
  linarith

end PlanarHalving.RankLimits

end OAI
