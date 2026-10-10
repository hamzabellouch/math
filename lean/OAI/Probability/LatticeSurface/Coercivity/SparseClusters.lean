import Mathlib

namespace OAI

open Set MeasureTheory

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def component (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Reachable x)

@[simp] lemma mem_component (G : SimpleGraph V) (x y : V) :
    y ∈ component G x ↔ G.Reachable x y := by simp [component]

omit [Fintype V] in
lemma walk_boundary {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (S : Finset V) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ a ∈ S, ∃ b, b ∉ S ∧ G.Adj a b ∧ b ∈ p.support := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨a, ha, b, hb, hab, hbp⟩ := ih hz hy
      exact ⟨a, ha, b, hb, hab, by simp [hbp]⟩
    · exact ⟨x, hx, z, hz, hxz, by simp⟩

lemma walk_mem_component {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    {z : V} (hz : z ∈ p.support) : z ∈ component G x := by
  exact (mem_component _ _ _).mpr (p.takeUntil z hz).reachable

lemma closed_walk_witness (G : SimpleGraph V) (x : V) (m : ℕ)
    (hm : m + 1 ≤ (component G x).card) :
    ∃ p : G.Walk x x, p.length = 2*m ∧ p.support.toFinset.card = m+1 := by
  classical
  induction m with
  | zero => exact ⟨.nil, rfl, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp, hc⟩ := ih (by omega)
    have hnot : ¬ component G x ⊆ p.support.toFinset := by
      intro h
      have hh := Finset.card_le_card h
      omega
    obtain ⟨y, hy, hyp⟩ := Finset.not_subset.mp hnot
    obtain ⟨w⟩ := (mem_component G x y).mp hy
    obtain ⟨a, ha, b, hb, hab, hbw⟩ := walk_boundary w p.support.toFinset
      (by simp) hyp
    have hap : a ∈ p.support := List.mem_toFinset.mp ha
    let q := p.takeUntil a hap
    let r := p.dropUntil a hap
    let p' := q.append (.cons hab (.cons hab.symm r))
    have hpr : q.append r = p := p.take_spec hap
    have hlen : q.length + r.length = p.length := by
      simpa only [SimpleGraph.Walk.length_append] using congrArg SimpleGraph.Walk.length hpr
    have hsup : p'.support.toFinset = insert b p.support.toFinset := by
      ext z
      have hpz : z ∈ p.support ↔ z ∈ q.support ∨ z ∈ r.support := by
        rw [← hpr, SimpleGraph.Walk.mem_support_append_iff]
      simp only [List.mem_toFinset, Finset.mem_insert, p', SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_cons, List.mem_cons, hpz]
      have ha : a ∈ q.support := q.end_mem_support
      grind
    refine ⟨p', ?_, ?_⟩
    · simp only [p', SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      omega
    · rw [hsup, Finset.card_insert_of_notMem hb, hc]

lemma card_walks_le (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ x, (Finset.univ.filter (G.Adj x)).card ≤ D) (n : ℕ) (x y : V) :
    (G.finsetWalkLength n x y).card ≤ D ^ n := by
  classical
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y
    · subst y; simp [SimpleGraph.finsetWalkLength]
    · simp [SimpleGraph.finsetWalkLength, h]
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc
      _ ≤ ∑ z : G.neighborSet x, ((G.finsetWalkLength n z y).map
          ⟨fun p => SimpleGraph.Walk.cons z.property p, fun p q h => by cases h; rfl⟩).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ : G.neighborSet x, D ^ n := by
        apply Finset.sum_le_sum; intro z _
        simpa only [Finset.card_map] using ih z y
      _ = (Finset.univ.filter (G.Adj x)).card * D ^ n := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp [Fintype.card_subtype]
      _ ≤ D ^ (n+1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ (hD x) |>.trans_eq (Nat.mul_comm _ _)

end SparseClusters

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma walk_all_bad {G : SimpleGraph V} (bad : Set V)
    (hb : ∀ x y, G.Adj x y → x ∈ bad ∧ y ∈ bad) {x y : V} (p : G.Walk x y)
    (hx : x ∈ bad) : ∀ z ∈ p.support, z ∈ bad := by
  induction p with
  | nil => simpa using hx
  | @cons x w y hxw p ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact ih (hb x w hxw).2 z hz

omit [Fintype V] [DecidableEq V] in
lemma walk_start_bad {G : SimpleGraph V} (bad : Set V)
    (hb : ∀ x y, G.Adj x y → x ∈ bad ∧ y ∈ bad) {x y : V} (p : G.Walk x y)
    (hp : 0 < p.length) : x ∈ bad := by
  cases p with
  | nil => simp at hp
  | cons h p => exact (hb _ _ h).1

lemma sparse_component_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ x, (Finset.univ.filter (G.Adj x)).card ≤ D)
    (H : Ω → SimpleGraph V) (bad : Ω → Set V) (hHG : ∀ ω, H ω ≤ G)
    (hbad : ∀ ω x y, (H ω).Adj x y → x ∈ bad ω ∧ y ∈ bad ω)
    (ρ : ENNReal) (hρ : ρ ≤ 1)
    (hsparse : ∀ S : Finset V, μ {ω | ∀ x ∈ S, x ∈ bad ω} ≤ ρ ^ S.card)
    (x : V) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | m+1 ≤ (component (H ω) x).card} ≤ ((D : ENNReal)^2 * ρ)^m := by
  classical
  let W := {p : G.Walk x x // p.length = 2*m}
  let E (p : W) : Set Ω := if m+1 ≤ p.val.support.toFinset.card then
    {ω | ∀ z ∈ p.val.support.toFinset, z ∈ bad ω} else ∅
  have hsub : {ω | m+1 ≤ (component (H ω) x).card} ⊆ ⋃ p : W, E p := by
    intro ω hω
    obtain ⟨p, hplen, hpcard⟩ := closed_walk_witness (H ω) x m hω
    let q : W := ⟨p.mapLe (hHG ω), by simpa using hplen⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    have hqc : q.val.support.toFinset.card = m+1 := by
      simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hpcard
    simp only [E, ite_eq_left hqc.ge, Set.mem_ofPred_eq]
    intro z hz
    have hz' : z ∈ p.support := by simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support, List.mem_toFinset] using hz
    exact walk_all_bad (bad ω) (hbad ω) p
      (walk_start_bad (bad ω) (hbad ω) p (by omega)) z hz'
  have hEp (p : W) : μ (E p) ≤ ρ ^ m := by
    dsimp [E]
    split_ifs with hp
    · exact (hsparse p.val.support.toFinset).trans (pow_le_pow_of_le_one bot_le hρ (by omega))
    · simp
  calc
    _ ≤ μ (⋃ p : W, E p) := measure_mono hsub
    _ ≤ ∑ p : W, μ (E p) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _ : W, ρ ^ m := Finset.sum_le_sum fun p _ => hEp p
    _ = (Fintype.card W : ENNReal) * ρ ^ m := by simp
    _ ≤ ((D ^ (2*m) : ℕ) : ENNReal) * ρ ^ m := by
      gcongr
      change Fintype.card {p : G.Walk x x | p.length = 2*m} ≤ _
      rw [SimpleGraph.card_set_walk_length_eq]
      exact card_walks_le G D hD (2*m) x x
    _ = _ := by rw [Nat.cast_pow, pow_mul, mul_pow]

omit [DecidableEq V] in
lemma card_le_fiber_mul_image {W : Type*} [DecidableEq W] (φ : V → W) (B : ℕ)
    (hB : ∀ w, (Finset.univ.filter fun x => φ x = w).card ≤ B) (S : Finset V) :
    S.card ≤ (S.image φ).card * B := by
  by_contra h
  obtain ⟨w, hw, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) (Nat.lt_of_not_ge h)
  have hsub : (S.filter fun x => φ x = w) ⊆ (Finset.univ.filter fun x => φ x = w) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  exact (not_lt_of_ge ((Finset.card_le_card hsub).trans (hB w))) hcard

lemma sparse_box_component_tail {Ω W : Type*} [MeasurableSpace Ω] [DecidableEq W]
    (μ : Measure Ω) (G : SimpleGraph V) [DecidableRel G.Adj] (D B : ℕ)
    (hD : ∀ x, (Finset.univ.filter (G.Adj x)).card ≤ D) (hBpos : 0 < B)
    (φ : V → W) (hB : ∀ w, (Finset.univ.filter fun x => φ x = w).card ≤ B)
    (H : Ω → SimpleGraph V) (bad : Ω → Set W) (hHG : ∀ ω, H ω ≤ G)
    (hbad : ∀ ω x y, (H ω).Adj x y → φ x ∈ bad ω ∧ φ y ∈ bad ω)
    (ρ : ENNReal) (hρ : ρ ≤ 1)
    (hsparse : ∀ S : Finset W, μ {ω | ∀ w ∈ S, w ∈ bad ω} ≤ ρ ^ S.card)
    (x : V) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | B*m+1 ≤ (component (H ω) x).card} ≤ ((D : ENNReal)^(2*B) * ρ)^m := by
  classical
  let Paths := {p : G.Walk x x // p.length = 2*(B*m)}
  let E (p : Paths) : Set Ω := if B*m+1 ≤ p.val.support.toFinset.card then
    {ω | ∀ w ∈ p.val.support.toFinset.image φ, w ∈ bad ω} else ∅
  have hsub : {ω | B*m+1 ≤ (component (H ω) x).card} ⊆ ⋃ p : Paths, E p := by
    intro ω hω
    obtain ⟨p, hplen, hpcard⟩ := closed_walk_witness (H ω) x (B*m) hω
    let q : Paths := ⟨p.mapLe (hHG ω), by simpa using hplen⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    have hqc : q.val.support.toFinset.card = B*m+1 := by
      simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hpcard
    simp only [E, ite_eq_left hqc.ge]
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hz' : z ∈ p.support := by
      simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support, List.mem_toFinset] using hz
    exact walk_all_bad (φ ⁻¹' bad ω) (hbad ω) p
      (walk_start_bad (φ ⁻¹' bad ω) (hbad ω) p (by nlinarith)) z hz'
  have hEp (p : Paths) : μ (E p) ≤ ρ ^ m := by
    dsimp [E]
    split_ifs with hp
    · have hfib := card_le_fiber_mul_image φ B hB p.val.support.toFinset
      have hc : m ≤ (p.val.support.toFinset.image φ).card := by nlinarith
      exact (hsparse _).trans (pow_le_pow_of_le_one bot_le hρ hc)
    · simp
  calc
    _ ≤ μ (⋃ p : Paths, E p) := measure_mono hsub
    _ ≤ ∑ p : Paths, μ (E p) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _ : Paths, ρ ^ m := Finset.sum_le_sum fun p _ => hEp p
    _ = (Fintype.card Paths : ENNReal) * ρ ^ m := by simp
    _ ≤ ((D ^ (2*(B*m)) : ℕ) : ENNReal) * ρ ^ m := by
      gcongr
      change Fintype.card {p : G.Walk x x | p.length = 2*(B*m)} ≤ _
      rw [SimpleGraph.card_set_walk_length_eq]
      exact card_walks_le G D hD (2*(B*m)) x x
    _ = _ := by rw [Nat.cast_pow, ← mul_assoc, pow_mul, mul_pow]

end SparseClusters

namespace SparseClusters

lemma measurable_graph_statistic {Ω V X : Type*} [MeasurableSpace Ω] [Fintype V]
    [MeasurableSpace X] (H : Ω → SimpleGraph V)
    (hH : ∀ x y, MeasurableSet {ω | (H ω).Adj x y}) (F : SimpleGraph V → X) :
    Measurable (fun ω => F (H ω)) := by
  classical
  have hfib (J : SimpleGraph V) : MeasurableSet {ω | H ω = J} := by
    have he : {ω | H ω = J} = {ω | ∀ x y, (H ω).Adj x y ↔ J.Adj x y} := by
      ext ω
      exact ⟨fun h x y => by rw [h], fun h => SimpleGraph.ext (funext fun x => funext fun y => propext (h x y))⟩
    rw [he]
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter; intro x
    apply MeasurableSet.iInter; intro y
    by_cases h : J.Adj x y
    · simpa only [h, iff_true] using hH x y
    · simpa only [h, iff_false, Set.compl_ofPred] using (hH x y).compl
  intro S hS
  have he : (fun ω => F (H ω)) ⁻¹' S = ⋃ J : SimpleGraph V,
      if F J ∈ S then {ω | H ω = J} else ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨H ω, by simp [h]⟩
    · rintro ⟨J, h⟩
      split_ifs at h with hh
      · have h' : H ω = J := h
        simpa only [h'] using hh
      · exact False.elim h
  rw [he]
  apply MeasurableSet.iUnion; intro J
  split_ifs with hh
  · exact hfib J
  · exact MeasurableSet.empty

lemma summable_box_moment (B k : ℕ) :
    Summable (fun m : ℕ => ((B : ℝ) * (m+1))^k * (1/2 : ℝ)^m) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
    (show ‖(1/2 : ℝ)‖ < 1 by norm_num)
  have hs' := ((summable_nat_add_iff 1).mpr hs).mul_left ((B : ℝ)^k * 2)
  apply hs'.congr
  intro m
  simp only [Nat.cast_add, Nat.cast_one, pow_succ, mul_pow]
  ring

noncomputable def boxMoment (B k : ℕ) : ℝ :=
  ∑' m : ℕ, ((B : ℝ) * (m+1))^k * (1/2 : ℝ)^m

lemma boxMoment_nonneg (B k : ℕ) : 0 ≤ boxMoment B k :=
  tsum_nonneg (fun m => by positivity)

lemma nat_moment_of_geometric_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : Ω → ℕ) (hH : Measurable H) (hpos : ∀ ω, 0 < H ω)
    (B : ℕ) (hB : 0 < B)
    (htail : ∀ m : ℕ, 1 ≤ m → μ {ω | B*m+1 ≤ H ω} ≤ (1/2 : ENNReal)^m)
    (k : ℕ) : ∫⁻ ω, (H ω : ENNReal)^k ∂μ ≤ ENNReal.ofReal (boxMoment B k) := by
  let F := fun ω => (H ω - 1) / B
  have hF : Measurable F := (measurable_of_countable (fun n : ℕ => (n-1)/B)).comp hH
  have hbound (ω) : H ω ≤ B * (F ω + 1) := by
    have hh := Nat.mod_lt (H ω - 1) hB
    have he := Nat.mod_add_div (H ω - 1) B
    dsimp [F]
    rw [Nat.mul_add, Nat.mul_one]
    have hp := hpos ω
    omega
  have hprob (m : ℕ) : μ (F ⁻¹' {m}) ≤ (1/2 : ENNReal)^m := by
    by_cases hm : m = 0
    · subst m; simpa using (prob_le_one (μ := μ) (s := F ⁻¹' {0}))
    · apply le_trans (measure_mono (show F ⁻¹' {m} ⊆ {ω | B*m+1 ≤ H ω} from ?_))
        (htail m (Nat.one_le_iff_ne_zero.mpr hm))
      intro ω hω
      change B*m+1 ≤ H ω
      have hd : (H ω - 1) / B = m := hω
      have hh := Nat.div_mul_le_self (H ω - 1) B
      have hp := hpos ω
      rw [hd, Nat.mul_comm] at hh
      omega
  calc
    _ ≤ ∫⁻ ω, (((B : ENNReal) * (F ω+1))^k) ∂μ := by
      apply lintegral_mono; intro ω
      exact pow_le_pow_left' (by exact_mod_cast hbound ω) k
    _ = ∫⁻ m : ℕ, (((B : ENNReal) * (m+1))^k) ∂(Measure.map F μ) :=
      (lintegral_map (μ := μ) (f := fun m : ℕ => ((B : ENNReal) * (m+1))^k) (measurable_of_countable _) hF).symm
    _ = ∑' m : ℕ, (((B : ENNReal) * (m+1))^k) * μ (F ⁻¹' {m}) := by
      rw [lintegral_countable']
      simp only [Measure.map_apply hF (measurableSet_singleton _)]
    _ ≤ ∑' m : ℕ, (((B : ENNReal) * (m+1))^k) * (1/2 : ENNReal)^m := by
      apply ENNReal.tsum_le_tsum; intro m
      exact mul_le_mul_right (hprob m) _
    _ = ENNReal.ofReal (boxMoment B k) := by
      rw [boxMoment, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (summable_box_moment B k)]
      congr 1; ext m
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      simp [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ m) (by norm_num : (0 : ℝ) ≤ 1)]

lemma nat_pow_measurable {Ω : Type*} [MeasurableSpace Ω] (H : Ω → ℕ)
    (hH : Measurable H) (k : ℕ) : Measurable (fun ω => (H ω : ℝ)^k) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ)^k)).comp hH

lemma nat_pow_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (H : Ω → ℕ) (hH : Measurable H) (N : ℕ) (hN : ∀ ω, H ω ≤ N)
    (k : ℕ) : Integrable (fun ω => (H ω : ℝ)^k) μ := by
  apply (integrable_const ((N : ℝ)^k)).mono' (nat_pow_measurable H hH k).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN ω) k

lemma nat_real_moment_of_geometric_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : Ω → ℕ) (hH : Measurable H) (hpos : ∀ ω, 0 < H ω)
    (B : ℕ) (hB : 0 < B)
    (htail : ∀ m : ℕ, 1 ≤ m → μ {ω | B*m+1 ≤ H ω} ≤ (1/2 : ENNReal)^m)
    (k : ℕ) : (∫ ω, (H ω : ℝ)^k ∂μ) ≤ boxMoment B k := by
  have hh := nat_moment_of_geometric_tail μ H hH hpos B hB htail k
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => by positivity)
    (nat_pow_measurable H hH k).aestronglyMeasurable]
  have he (ω) : ENNReal.ofReal ((H ω : ℝ)^k) = (H ω : ENNReal)^k := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  simp_rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq
    (ENNReal.toReal_ofReal (boxMoment_nonneg B k))

lemma maximum_nat_moment_bound {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : V → Ω → ℕ)
    (hH : ∀ x, Measurable (H x)) (N : ℕ) (hN : ∀ x ω, H x ω ≤ N)
    (k : ℕ) (_hk : 0 < k) (C R : ℝ) (hR : 0 < R)
    (hmoment : ∀ x, (∫ ω, (H x ω : ℝ)^k ∂μ) ≤ C) :
    μ.real {ω | ∃ x, R < (H x ω : ℝ)} ≤ (Fintype.card V : ℝ) * C / R^k := by
  have hRp : 0 < R^k := pow_pos hR k
  have hsingle (x : V) : μ.real {ω | R < (H x ω : ℝ)} ≤ C / R^k := by
    apply (le_div_iff₀ hRp).mpr
    have hs : {ω | R < (H x ω : ℝ)} ⊆ {ω | R^k ≤ (H x ω : ℝ)^k} := by
      intro ω hω
      exact pow_le_pow_left₀ hR.le hω.le k
    have hm := measureReal_mono (μ := μ) hs
    have hh := mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ω => (H x ω : ℝ)^k)
      (Filter.Eventually.of_forall fun ω => by positivity)
      (nat_pow_integrable_of_bound μ (H x) (hH x) N (hN x) k) (R^k)
    nlinarith [hmoment x]
  rw [show {ω | ∃ x, R < (H x ω : ℝ)} = ⋃ x, {ω | R < (H x ω : ℝ)} by ext; simp]
  calc
    _ ≤ ∑ x : V, μ.real {ω | R < (H x ω : ℝ)} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : V, C / R^k := Finset.sum_le_sum fun x _ => hsingle x
    _ = _ := by simp [mul_div_assoc]

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma reachable_of_edge_reachable (H : SimpleGraph V) (K : SimpleGraph W) (φ : V → W)
    (he : ∀ x y, H.Adj x y → K.Reachable (φ x) (φ y)) {x y : V}
    (hxy : H.Reachable x y) : K.Reachable (φ x) (φ y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih => exact (he _ _ h).trans ih

lemma component_card_le_cover (H : SimpleGraph V) (K : SimpleGraph W)
    (φ : V → W) (B : ℕ)
    (hB : ∀ w, (Finset.univ.filter fun x => φ x = w).card ≤ B)
    (he : ∀ x y, H.Adj x y → K.Reachable (φ x) (φ y)) (x : V) :
    (component H x).card ≤ B * (component K (φ x)).card := by
  have hsub : (component H x).image φ ⊆ component K (φ x) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact (mem_component _ _ _).mpr
      (reachable_of_edge_reachable H K φ he ((mem_component _ _ _).mp hy))
  exact (card_le_fiber_mul_image φ B hB _).trans
    ((Nat.mul_le_mul_right B (Finset.card_le_card hsub)).trans_eq (Nat.mul_comm _ _))

noncomputable def badBoxGraph (K : SimpleGraph W) (bad : Set W) : SimpleGraph W where
  Adj x y := K.Adj x y ∧ x ∈ bad ∧ y ∈ bad
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => K.irrefl h.1⟩

lemma sparse_cover_component_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : SimpleGraph W) [DecidableRel K.Adj] (Db B : ℕ)
    (hDb : ∀ w, (Finset.univ.filter (K.Adj w)).card ≤ Db)
    (φ : V → W) (hB : ∀ w, (Finset.univ.filter fun x => φ x = w).card ≤ B)
    (H : Ω → SimpleGraph V) (bad : Ω → Set W)
    (hcover : ∀ ω x y, (H ω).Adj x y → φ x = φ y ∨ K.Adj (φ x) (φ y))
    (hbad : ∀ ω x y, (H ω).Adj x y → φ x ∈ bad ω ∧ φ y ∈ bad ω)
    (ρ : ENNReal) (hρ : ρ ≤ 1)
    (hsparse : ∀ S : Finset W, μ {ω | ∀ w ∈ S, w ∈ bad ω} ≤ ρ ^ S.card)
    (x : V) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | B*m+1 ≤ (component (H ω) x).card} ≤ ((Db : ENNReal)^2 * ρ)^m := by
  have he (ω x y) (hxy : (H ω).Adj x y) :
      (badBoxGraph K (bad ω)).Reachable (φ x) (φ y) := by
    rcases hcover ω x y hxy with hh | hh
    · simpa only [hh] using (SimpleGraph.Reachable.refl (φ y) : (badBoxGraph K (bad ω)).Reachable (φ y) (φ y))
    · exact SimpleGraph.Adj.reachable ⟨hh, hbad ω x y hxy⟩
  have hsub : {ω | B*m+1 ≤ (component (H ω) x).card} ⊆
      {ω | m+1 ≤ (component (badBoxGraph K (bad ω)) (φ x)).card} := by
    intro ω hω
    have hc := component_card_le_cover (H ω) (badBoxGraph K (bad ω)) φ B hB (he ω) x
    change B*m+1 ≤ (component (H ω) x).card at hω
    change m+1 ≤ _
    by_contra hh
    have hle : (component (badBoxGraph K (bad ω)) (φ x)).card ≤ m := by omega
    have hmul := Nat.mul_le_mul_left B hle
    omega
  apply (measure_mono hsub).trans
  exact sparse_component_tail μ K Db hDb (fun ω => badBoxGraph K (bad ω)) bad
    (fun ω x y h => h.1) (fun ω x y h => h.2) ρ hρ hsparse (φ x) m hm

end SparseClusters

end OAI
