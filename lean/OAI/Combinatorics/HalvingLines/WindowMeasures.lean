import OAI.Combinatorics.HalvingLines.Sweep

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def Data.conditional (L : Data) : Kernel Labels I :=
  (L.edgeTime : Measure (Labels×I)).condKernel
instance (L : Data) : IsMarkovKernel L.conditional := by
  unfold Data.conditional
  infer_instance

lemma Data.edge_toMeasure (L : Data) : (L.edge : Measure Labels)=(L.edgeTime : Measure (Labels×I)).fst := by
  rw [Data.edge,FiniteMeasure.toMeasure_map]
  rfl

lemma Data.conditional_measurable (L : Data) (J : Window) :
    Measurable (fun z => (L.conditional z).real (carrier J)) :=
  (L.conditional.measurable_coe (measurable_carrier J)).ennreal_toReal

lemma Converges.conditional_integral {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)=∫ z in U, (L.conditional z).real (carrier J) ∂(L.edge : Measure Labels) := by
  have hi := Measure.setIntegral_condKernel (ρ:=(L.edgeTime : Measure (Labels×I)))
    (f:=fun _ => (1:ℝ)) hU (measurable_carrier J) (integrable_const 1)
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one] at hi
  rw [L.edge_toMeasure]
  change (L.edgeWindow J U : ℝ)=∫ z in U, ((L.edgeTime : Measure (Labels×I)).condKernel z).real (carrier J)
    ∂(L.edgeTime : Measure (Labels×I)).fst
  rw [hi]
  change ((L.edgeWindow J : Measure Labels) U).toReal= _
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

lemma Converges.edgeWindow_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    ((L.edgeWindow J).mass : ℝ)=((2^J.1 : ℕ) : ℝ)⁻¹ := by
  have he := h.restriction_mass hR J
  have hm : (L.edgeWindow J).mass=(L.timeRestrict J).mass := by
    change (L.timeRestrict J).map Prod.fst univ=(L.timeRestrict J) univ
    rw [FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,preimage_univ]
  rw [hm]
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.coe_toReal,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    Nat.cast_pow,Nat.cast_ofNat] using hh

lemma Data.conditional_le_one (L : Data) (J : Window) (z : Labels) :
    (L.conditional z).real (carrier J)≤1 := by
  exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

lemma Data.conditional_sum (L : Data) (m : ℕ) (z : Labels) :
    ∑ i : Fin (2^m), (L.conditional z).real (carrier ⟨m,i⟩)=1 := by
  have he : (⋃ i : Fin (2^m),carrier ⟨m,i⟩)=univ := UniformPartition.cells_cover (2^m)
  have hd : Pairwise (fun (i j : Fin (2^m)) => Disjoint (carrier ⟨m,i⟩) (carrier ⟨m,j⟩)) :=
    UniformPartition.cells_disjoint (2^m)
  rw [← measureReal_iUnion_fintype hd (fun i => measurable_carrier ⟨m,i⟩),he]
  simp

end PlanarHalving.RankLimits

namespace PlanarHalving.Sweep
open Set

lemma activity_family_cubic {n k : ℕ} (P : Fin n → Point) (hP : Generic P)
    [NeZero n] (hk : k≤n) {b : ℕ} (hb : 0<b)
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (u v : ι → Fin ((traversal (criticalSlopes P)).size+1))
    (huv : ∀ i∈D, u i≤v i)
    (hdisjoint : ∀ i∈D, ∀ j∈D, i≠j → Disjoint (Ioc (u i) (v i)) (Ioc (u j) (v j)))
    (hactivity : ∀ i, ∀ hi : i∈D, b≤((states P hP hk).intervalActivity (u i) (v i) (huv i hi)).card) :
    (D.card : ℝ)^3*(b : ℝ)^4≤10000000000*(n : ℝ)^4 := by
  classical
  let f := fun i => (u i,v i)
  have hlt (i) (hi : i∈D) : u i<v i := by
    apply lt_of_le_of_ne (huv i hi)
    intro he
    have ha := (states P hP hk).intervalActivity_pos_distance (huv i hi) (hb.trans_le (hactivity i hi))
    rw [he,States.distance_self] at ha
    omega
  have hinj : Set.InjOn f D := by
    intro i hi j hj he
    by_contra hne
    have hu : u i=u j := congrArg Prod.fst he
    have hv : v i=v j := congrArg Prod.snd he
    exact Set.disjoint_left.mp (hdisjoint i hi j hj hne)
      (show v i∈Ioc (u i) (v i) from ⟨hlt i hi,le_rfl⟩)
      (by rw [hv,hu] at *; exact ⟨hlt j hj,le_rfl⟩)
  have hh := activity_packing_cubic P hP hk hb (D.image f) ?_ ?_ ?_
  · rwa [Finset.card_image_iff.mpr hinj] at hh
  · intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    exact hdisjoint i hi j hj (fun he => hpq (congrArg f he))
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact huv i hi
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hactivity i hi

lemma cubic_to_tail {x u : ℝ} (hx : 0≤x) (hu : 0<u)
    (h : x^3*u^4≤10000000000) : x≤10000*u^(-(4:ℝ)/3) := by
  have hp : (u^(-(4:ℝ)/3))^3=u^(-(4:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hu.le]
    norm_num
  have he : u^(-(4:ℝ))=(u^4)⁻¹ := by rw [Real.rpow_neg hu.le]; norm_num
  have hpos : 0≤10000*u^(-(4:ℝ)/3) := by positivity
  apply (pow_le_pow_iff_left₀ hx hpos (by omega : (3:ℕ)≠0)).mp
  rw [mul_pow,hp,he]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hu 4)).mpr (h.trans (by norm_num : (10000000000:ℝ)≤10000^3))

end PlanarHalving.Sweep

namespace PlanarHalving.Batches
open Set Sweep
variable {n R k a T : ℕ} {P : Fin n → Point}

lemma System.vertices_subset_activity (S : @System n R k a P) (H : @States n T k P)
    (index : Fin (R+1) → Fin (T+1)) (hm : Monotone index)
    (hmarks : ∀ j, S.marks j=H.marks (index j)) :
    S.vertices ⊆ H.intervalActivity (index 0) (index (Fin.last R))
      (hm (Fin.zero_le _)) := by
  classical
  have he (b : Fin R) (x : Fin n)
      (hx : (x∈S.marks b.castSucc ∧ x∉S.marks b.succ) ∨
            (x∉S.marks b.castSucc ∧ x∈S.marks b.succ)) :
      x∈H.intervalActivity (index 0) (index (Fin.last R)) (hm (Fin.zero_le _)) := by
    rw [States.mem_intervalActivity]
    rw [hmarks,hmarks] at hx
    by_cases hx0 : x∈H.marks (index 0)
    · rcases hx with hx | hx
      · exact ⟨index b.succ,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inr ⟨hx.2,hx0⟩⟩
      · exact ⟨index b.castSucc,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inr ⟨hx.1,hx0⟩⟩
    · rcases hx with hx | hx
      · exact ⟨index b.castSucc,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inl ⟨hx.1,hx0⟩⟩
      · exact ⟨index b.succ,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inl ⟨hx.2,hx0⟩⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨e,he',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,_⟩ := (S.mem_edges e).mp he'
    exact he b e.1 (Or.inl (Finset.mem_sdiff.mp hb))
  · obtain ⟨e,he',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,hb⟩ := (S.mem_edges e).mp he'
    exact he b e.2 (Or.inr (And.symm (Finset.mem_sdiff.mp hb)))

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Sweep Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

structure Configuration.SweepEmbedding (F : Configuration) where
  rank_le : F.k≤F.n
  index : Fin (F.R+1) → Fin ((traversal (criticalSlopes F.point)).size+1)
  increasing : StrictMono index
  marks : ∀ j, F.system.marks j=(states F.point F.generic rank_le).marks (index j)

noncomputable def Configuration.SweepEmbedding.start {F : Configuration} (E : F.SweepEmbedding) (J : Window) :=
  E.index ⟨TimeWindows.start F.R J,lt_of_le_of_lt ((start_le_stop F.R J).trans (stop_le F.R J)) (Nat.lt_succ_self _)⟩
noncomputable def Configuration.SweepEmbedding.stop {F : Configuration} (E : F.SweepEmbedding) (J : Window) :=
  E.index ⟨TimeWindows.stop F.R J,lt_of_le_of_lt (stop_le F.R J) (Nat.lt_succ_self _)⟩

lemma Configuration.SweepEmbedding.start_le_stop {F : Configuration} (E : F.SweepEmbedding) (J : Window) :
    E.start J≤E.stop J := E.increasing.monotone (TimeWindows.start_le_stop F.R J)

lemma Configuration.SweepEmbedding.stop_le_start {F : Configuration} (E : F.SweepEmbedding)
    {A B : Window} (hAB : Before A B) : E.stop A≤E.start B :=
  E.increasing.monotone (TimeWindows.stop_le_start F.R hAB)

lemma Configuration.SweepEmbedding.vertices_subset {F : Configuration} (E : F.SweepEmbedding) (J : Window) :
    (F.system.timeWindow J).vertices ⊆ (states F.point F.generic E.rank_le).intervalActivity
      (E.start J) (E.stop J) (E.start_le_stop J) := by
  let index : Fin (length F.R J+1) → Fin ((traversal (criticalSlopes F.point)).size+1) :=
    fun j => E.index ⟨TimeWindows.start F.R J+j.val,by have:=start_add_length F.R J;have:=stop_le F.R J;have:=j.isLt;omega⟩
  have hmono : Monotone index := by
    intro i j hij
    apply E.increasing.monotone
    exact Nat.add_le_add_left hij _
  have he := (F.system.timeWindow J).vertices_subset_activity
    (states F.point F.generic E.rank_le) index hmono (fun j => E.marks _)
  have hstart : index 0=E.start J := by congr 1
  have hstop : index (Fin.last (length F.R J))=E.stop J := by
    apply congrArg E.index
    apply Fin.ext
    exact start_add_length F.R J
  simpa only [hstart,hstop] using he

lemma before_of_same_depth {m : ℕ} {i j : Fin (2^m)} (hij : i<j) : Before ⟨m,i⟩ ⟨m,j⟩ := by
  change ((i.val+1 : ℕ) : ℝ)/(2^m : ℕ)≤(j : ℝ)/(2^m : ℕ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show i.val+1≤j.val from hij)

lemma Configuration.SweepEmbedding.windows_disjoint {F : Configuration} (E : F.SweepEmbedding)
    {m : ℕ} {i j : Fin (2^m)} (hij : i≠j) :
    Disjoint (Ioc (E.start ⟨m,i⟩) (E.stop ⟨m,i⟩)) (Ioc (E.start ⟨m,j⟩) (E.stop ⟨m,j⟩)) := by
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hi.2.trans (E.stop_le_start (before_of_same_depth hh))) hj.1)
  · exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hj.2.trans (E.stop_le_start (before_of_same_depth hh))) hi.1)

lemma Configuration.SweepEmbedding.activity_tail {F : Configuration} (E : F.SweepEmbedding)
    (m : ℕ) {u : ℝ} (hu : 0<u) :
    (((Finset.univ.filter fun i : Fin (2^m) => u<((F.vertices ⟨m,i⟩).mass : ℝ)).card : ℝ))≤
      10000*u^(-(4:ℝ)/3) := by
  classical
  let D := Finset.univ.filter fun i : Fin (2^m) => u<((F.vertices ⟨m,i⟩).mass : ℝ)
  let b := ⌊u*(F.n : ℝ)⌋₊+1
  have hb : 0<b := by dsimp [b];omega
  have hn : (0:ℝ)<F.n := Nat.cast_pos.mpr F.n_pos
  have hcard (i) (hi : i∈D) : b≤(F.system.timeWindow ⟨m,i⟩).vertices.card := by
    have hi' := (Finset.mem_filter.mp hi).2
    rw [F.vertices_mass_ratio] at hi'
    have hlt := (lt_div_iff₀ hn).mp hi'
    change ⌊u*(F.n : ℝ)⌋₊+1≤_
    exact Nat.succ_le_of_lt ((Nat.floor_lt (mul_nonneg hu.le hn.le)).mpr hlt)
  have hh := activity_family_cubic F.point F.generic E.rank_le hb D
    (fun i => E.start ⟨m,i⟩) (fun i => E.stop ⟨m,i⟩)
    (fun i _hi => E.start_le_stop ⟨m,i⟩)
    (fun _i _hi _j _hj hij => E.windows_disjoint hij)
    (fun i hi => (hcard i hi).trans (Finset.card_le_card (E.vertices_subset ⟨m,i⟩)))
  have hb' : u*(F.n : ℝ)≤(b : ℝ) := by
    dsimp [b]
    rw [Nat.cast_add,Nat.cast_one]
    exact (Nat.lt_floor_add_one _).le
  have hh' : (D.card : ℝ)^3*(u*(F.n : ℝ))^4≤10000000000*(F.n : ℝ)^4 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hu.le hn.le) hb' 4) (by positivity)).trans hh
  have hcub : (D.card : ℝ)^3*u^4≤10000000000 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hn 4)).mp
    nlinarith [hh']
  exact cubic_to_tail (by positivity) hu hcub

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.activity_tail {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (m : ℕ) {u : ℝ} (hu : 0<u) :
    (((Finset.univ.filter fun i : Fin (2^m) => u<((L.vertices ⟨m,i⟩).mass : ℝ)).card : ℝ))≤
      10000*u^(-(4:ℝ)/3) := by
  classical
  have hh : ∀ᶠ j in atTop, ∀ i : Fin (2^m), u<((L.vertices ⟨m,i⟩).mass : ℝ) →
      u<(((F j).vertices ⟨m,i⟩).mass : ℝ) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : u<((L.vertices ⟨m,i⟩).mass : ℝ)
    · have hm := NNReal.continuous_coe.tendsto _ |>.comp
        (FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices ⟨m,i⟩))
      exact ((tendsto_order.mp hm).1 u hi).mono (fun j hj _ => hj)
    · exact Eventually.of_forall (fun _ => fun hh => (hi hh).elim)
  obtain ⟨j,hj⟩ := hh.exists
  apply le_trans _ ((E j).activity_tail m hu)
  have hs : (Finset.univ.filter fun i : Fin (2^m) => u<((L.vertices ⟨m,i⟩).mass : ℝ)) ⊆
      (Finset.univ.filter fun i : Fin (2^m) => u<(((F j).vertices ⟨m,i⟩).mass : ℝ)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj i (Finset.mem_filter.mp hi).2⟩
  exact Nat.cast_le.mpr (Finset.card_le_card hs)

noncomputable def timePartition (m : ℕ) : Finset Window :=
  Finset.univ.image (fun i : Fin (2^m) => (⟨m,i⟩ : Window))

lemma timePartition_card (m : ℕ) : (timePartition m).card=2^m := by
  classical
  rw [timePartition,Finset.card_image_of_injective _ (fun _ _ he => eq_of_heq (Sigma.mk.inj he).2),Finset.card_univ,Fintype.card_fin]

lemma timePartition_cover (m : ℕ) (t : I) : ∃ J∈timePartition m, t∈carrier J := by
  have ht : t∈⋃ i : Fin (2^m),carrier ⟨m,i⟩ := by
    change t∈⋃ i : Fin (2^m), UniformPartition.cell (2^m) i
    rw [UniformPartition.cells_cover];trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  exact ⟨⟨m,i⟩,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩

lemma sum_timePartition {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Window → M) :
    ∑ J∈timePartition m, f J = ∑ i : Fin (2^m), f ⟨m,i⟩ := by
  classical
  exact Finset.sum_image (fun _ _ _ _ he => eq_of_heq (Sigma.mk.inj he).2)

lemma filter_timePartition (m : ℕ) (p : Window → Prop) [DecidablePred p] :
    (timePartition m |>.filter p).card = (Finset.univ.filter fun i : Fin (2^m) => p ⟨m,i⟩).card := by
  classical
  rw [timePartition,Finset.filter_image,Finset.card_image_of_injective _ (fun _ _ he => eq_of_heq (Sigma.mk.inj he).2)]

lemma Converges.conditional_nullSingleton {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4 /
      (((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3 /
      (((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0)) :
    ∀ᵐ z ∂(L.edge : Measure Labels), NullSingletonClass (L.conditional z) := by
  classical
  apply kernel_nullSingleton_of_cells (L.edge : Measure Labels) L.conditional timePartition
    (fun _ J => carrier J) timePartition_cover
  intro b
  apply ae_exists_partition_small L.edge L.points timePartition
    (fun _ J z => (L.conditional z).real (carrier J)) (fun _ => L.vertices) (fun _ => L.edgeWindow)
    (fun _ J => ((L.vertices J).mass : ℝ)) (fun m => (2:ℝ)^m) hC
    (fun _ => by positivity) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  · intro m
    rw [timePartition_card,Nat.cast_pow,Nat.cast_ofNat]
  · exact fun _ J _ => L.conditional_measurable J
  · exact fun _ _ _ _ => measureReal_nonneg
  · exact fun _ J _ => L.conditional_le_one J
  · intro m z
    rw [sum_timePartition,L.conditional_sum]
  · exact fun _ _ _ => NNReal.coe_nonneg _
  · intro _ J _ U
    have hh := (h.vertices_le_points J) U
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
    exact ENNReal.coe_le_coe.mp hh
  · exact fun _ J _ U hU => h.conditional_integral hR J hU
  · intro m J hJ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hJ
    rw [h.edgeWindow_mass hR,Nat.cast_pow,Nat.cast_ofNat]
  · exact fun _ J _ U hU => h.local_cubic hC hcoeff herror J hU
  · intro m u hu
    rw [filter_timePartition]
    exact h.activity_tail E m hu
  · positivity

end PlanarHalving.RankLimits
namespace PlanarHalving.PlaneGraph
open Set
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.pointOfPair (D : Drawing P) (w : (V×V)×(V×V)) : Point := by
  classical
  exact if h : w∈D.crossings then D.crossingPoint ⟨w,h⟩ else 0

lemma Drawing.pointOfPair_eq (D : Drawing P) (w : ↥D.crossings) :
    D.pointOfPair w.val=D.crossingPoint w := by
  classical
  simp only [Drawing.pointOfPair,dite_eq_left w.property]

end PlanarHalving.PlaneGraph
namespace PlanarHalving.Batches
open Set PlaneGraph TimeWindows MeasureTheory Limits
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.restricted_crossing (S : @System n R k a P) (hP : Generic P)
    (E : Finset (Fin n×Fin n)) (hE : E⊆S.edges) :
    (E.card : ℝ)^3 ≤ 2304*(n : ℝ)^2*((S.drawing.restrictEdges E).crossings.card : ℝ)+13824*(n : ℝ)^3 := by
  classical
  let D := S.drawing.restrictEdges E
  have he : D.edges=E := by
    ext e
    simp only [D, Drawing.restrictEdges, Finset.mem_inter]
    exact ⟨And.right, fun h => ⟨hE h, h⟩⟩
  have hc := D.designated_crossing hP.1 (Generic.x_injective hP) D.vertices (by rfl)
    (fun e he => Or.inl (D.ends e he).1)
  have hv : (D.vertices.card : ℝ) ≤ n := Nat.cast_le.mpr S.vertices_le
  rw [he] at hc
  apply hc.trans
  nlinarith [mul_le_mul_of_nonneg_right (sq_le_sq₀ (by positivity) (by positivity) |>.mpr hv)
    (by positivity : (0:ℝ) ≤ 2304*((D.crossings.card : ℝ))),
    pow_le_pow_left₀ (by positivity) hv 3]

noncomputable def System.crossingsIn (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} (z : Point → X) (U : Set X) := by
  classical
  exact (S.windowCrossings A B).filter (fun w => z (S.drawing.pointOfPair w)∈U)

lemma System.windowCrossMeasure_apply (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) {U : Set X} (hU : MeasurableSet U) :
    (S.windowCrossMeasure A B z U : ℝ)=(S.crossingsIn A B z U).card/((a*n : ℕ) : ℝ)^2 := by
  classical
  rw [System.windowCrossMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter (fun w : ↥(S.windowCrossings A B) => z (S.windowCrossPoint A B w)∈U)).card=
      (S.crossingsIn A B z U).card := by
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,System.crossingsIn]
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨v.property,?_⟩
      simpa only [System.windowCrossPoint,Drawing.pointOfPair,
        dite_eq_left (S.windowCrossings_sub A B v.property)] using hv
    · rintro ⟨hw,hz⟩
      refine ⟨⟨w,hw⟩,?_,rfl⟩
      simpa only [System.windowCrossPoint,Drawing.pointOfPair,
        dite_eq_left (S.windowCrossings_sub A B hw)] using hz
  rw [he]
  simp only [NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast,div_eq_inv_mul]

lemma System.retained_crossing_cover (S : @System n R k a P) [NeZero R]
    {X : Type*} (z : Point → X) (U : Set X) (W : Finset Window)
    (E : Finset (Fin n×Fin n)) (_hE : E⊆S.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(S.timeWindow J).edges)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (P e.1) (P e.2), z p∈U) :
    (S.drawing.restrictEdges E).crossings ⊆ (W×ˢ W).biUnion
      (fun ij => if ij.1=ij.2 then (S.timeWindow ij.1).drawing.crossings
        else S.crossingsIn ij.1 ij.2 z U) := by
  classical
  intro w hw
  have hp := (S.drawing.restrictEdges E).crossing_props ⟨w,hw⟩
  have hep := hp
  simp only [Drawing.restrictEdges, Finset.mem_inter] at hep
  have he₁ := hep.1.2
  have he₂ := hep.2.1.2
  obtain ⟨J,hJ,heJ⟩ := hcover w.1 he₁
  obtain ⟨K,hK,heK⟩ := hcover w.2 he₂
  apply Finset.mem_biUnion.mpr
  refine ⟨(J,K),Finset.mem_product.mpr ⟨hJ,hK⟩,?_⟩
  dsimp only
  by_cases hJK : J=K
  · rw [ite_eq_left hJK]
    rw [← hJK] at heK
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heJ,heK⟩,hp.2.2⟩
  · rw [ite_eq_right hJK]
    have hc : w∈S.drawing.crossings := S.drawing.restrict_crossings E hw
    have hz : z (S.drawing.pointOfPair w)∈U := by
      rw [show S.drawing.pointOfPair w=S.drawing.crossingPoint ⟨w,hc⟩ from S.drawing.pointOfPair_eq ⟨w,hc⟩]
      exact hnear _ he₁ _ ((openSegment_subset_segment ℝ _ _) (S.drawing.crossingPoint_mem ⟨w,hc⟩).1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hc,Or.inl ⟨heJ,heK⟩⟩,hz⟩

lemma System.retained_crossing_bound (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) {U : Set X} (hU : MeasurableSet U) (W : Finset Window)
    (E : Finset (Fin n×Fin n)) (hE : E⊆S.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(S.timeWindow J).edges)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (P e.1) (P e.2), z p∈U) :
    (((S.drawing.restrictEdges E).crossings.card : ℝ)/((a*n : ℕ) : ℝ)^2)  ≤
      ∑ J∈W, ∑ K∈W, if J=K then 2*((S.timeWindow J).vertices.card : ℝ)^2/(n : ℝ)^2
        else (S.windowCrossMeasure J K z U : ℝ) := by
  classical
  have hc := (Finset.card_le_card (S.retained_crossing_cover z U W E hE hcover hnear)).trans
    (Finset.card_biUnion_le)
  have hh : ((S.drawing.restrictEdges E).crossings.card : ℝ) ≤
      ∑ ij∈W×ˢ W, if ij.1=ij.2 then 2*(a : ℝ)^2*((S.timeWindow ij.1).vertices.card : ℝ)^2
        else ((S.crossingsIn ij.1 ij.2 z U).card : ℝ) := by
    apply (Nat.cast_le.mpr hc).trans
    push_cast
    apply Finset.sum_le_sum
    intro ij _hij
    split_ifs with he
    · exact_mod_cast (S.timeWindow ij.1).crossing_cap hP.1 (Generic.x_injective hP)
        ((S.timeWindow ij.1).drawing.noMultiple_of_generic hP)
    · rfl
  apply (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq
  rw [Finset.sum_div,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro J _hJ
  apply Finset.sum_congr rfl
  intro K _hK
  split_ifs
  · have ha : (a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
    push_cast
    field_simp
  · exact (S.windowCrossMeasure_apply J K z hU).symm

end PlanarHalving.Batches

end OAI
