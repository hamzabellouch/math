import OAI.Computability.WLIdentification.AcceptingBroadcast

namespace OAI

namespace WLIdentification

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

abbrev primaryTruth (p : C.Primary) (a : Fin r → Bool) : Fin (C.primaryDimension p) → Prop :=
  match p with
  | none => fun _ => False
  | some p => C.PortTrue p a

abbrev primarySet (p : C.Primary) (a : Fin r → Bool) :=
  BufferAlgebra.truthVectors (C.primaryTruth p a)

abbrev sourceTruth (l : C.Connection) (a : Fin r → Bool) : Prop := match l with
  | .original e => C.True (C.source e) a
  | .test t => C.True (C.testType t) a
  | .flip _ => False
  | .broadcast _ _ => False
  | .self p j => C.primaryTruth p a j
  | .conflict => False

abbrev targetTruth (l : C.Connection) (a : Fin r → Bool) : Prop := match l with
  | .original e => C.PortTrue (C.target e) a (C.port e)
  | .test _ => False
  | .flip _ => False
  | .broadcast p j => C.PortTrue p a j
  | .self p j => C.primaryTruth p a j
  | .conflict => False

def rejectConstant : C.Comparison → Bit
  | .third .conflict => 1
  | _ => 0

theorem source_truth_image (l : C.Connection) (a : Fin r → Bool) :
    C.sourceForm l '' C.primarySet (C.connectionSource l) a =
      @ite (Set Bit) (C.sourceTruth l a) (Classical.propDecidable _) {0} Set.univ := by
  classical
  have hs (p : P) : ⇑(sumForm (C.dimension p)) = fun v => ∑ j, v j :=
    funext (sumForm_apply _)
  cases l with
  | original e =>
    rw [hs]
    have hu := BufferAlgebra.sum_truth (C.PortTrue (C.source e) a)
    by_cases ht : ∀ j, C.PortTrue (C.source e) a j <;>
      simpa only [sourceTruth, True, connectionSource, primarySet, primaryTruth, ht, ite_true, ite_false] using hu
  | test t =>
    rw [hs]
    have hu := BufferAlgebra.sum_truth (C.PortTrue (C.testType t) a)
    by_cases ht : ∀ j, C.PortTrue (C.testType t) a j <;>
      simpa only [sourceTruth, True, connectionSource, primarySet, primaryTruth, ht, ite_true, ite_false] using hu
  | flip i => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | broadcast p j => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | self p j => exact BufferAlgebra.projection_truth (C.primaryTruth p a) j
  | conflict => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0

theorem target_truth_image (l : C.Connection) (a : Fin r → Bool) :
    C.targetForm l '' C.primarySet (C.connectionTarget l) a =
      @ite (Set Bit) (C.targetTruth l a) (Classical.propDecidable _) {0} Set.univ := by
  classical
  cases l with
  | original e => exact BufferAlgebra.projection_truth (C.PortTrue (C.target e) a) (C.port e)
  | test t => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | flip i => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | broadcast p j => exact BufferAlgebra.projection_truth (C.PortTrue p a) j
  | self p j => exact BufferAlgebra.projection_truth (C.primaryTruth p a) j
  | conflict => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0

theorem source_implies_target (h : ¬ C.Accepted) (l : C.Connection)
    (a : (C.connectionMap l).Point) (ht : C.sourceTruth l ((C.connectionMap l).source a)) :
    C.targetTruth l ((C.connectionMap l).target a) ∧ C.rejectConstant (.third l) = 0 := by
  cases l with
  | original e => exact ⟨PortTrue.edge e a ht, rfl⟩
  | test t => exact (h ⟨t, a, ht⟩).elim
  | flip i => exact ht.elim
  | broadcast p j => exact ht.elim
  | self p j => exact ⟨ht, rfl⟩
  | conflict => exact ht.elim

def rejectDestination (l : C.Connection) (a : Fin r → Bool) : Set Bit :=
  (fun v => C.rejectConstant (.third l) + C.targetForm l v) ''
    C.primarySet (C.connectionTarget l) (fun i => (C.connectionMap l).mapping i (a i))

theorem rejectDestination_nonempty (l : C.Connection) (a : Fin r → Bool) :
    (C.rejectDestination l a).Nonempty :=
  (BufferAlgebra.truthVectors_nonempty _).image _

theorem rejectDestination_true (h : ¬ C.Accepted) (l : C.Connection)
    (a : (C.connectionMap l).Point) (ht : C.sourceTruth l ((C.connectionMap l).source a)) :
    C.rejectDestination l ((C.connectionMap l).source a) = {0} := by
  obtain ⟨hd, hb⟩ := C.source_implies_target h l a ht
  dsimp only [rejectDestination]
  rw [hb]
  simp only [zero_add]
  change C.targetForm l '' C.primarySet (C.connectionTarget l) ((C.connectionMap l).target a) = _
  rw [C.target_truth_image l _, ite_eq_left hd]

noncomputable def rejectBuffer (l : C.Connection) (a : Fin r → Bool) : Set (Fin 2 → Bit) := by
  classical
  exact if C.sourceTruth l a then {0} else BufferAlgebra.correlated (C.rejectDestination l a)

theorem rejectBuffer_nonempty (l : C.Connection) (a : Fin r → Bool) :
    (C.rejectBuffer l a).Nonempty := by
  classical
  unfold rejectBuffer
  split
  · exact Set.singleton_nonempty _
  · exact BufferAlgebra.correlated_nonempty (C.rejectDestination_nonempty l a)

theorem rejectBuffer_projection (l : C.Connection) (a : Fin r → Bool) (j : Fin 2) :
    (fun v => v j) '' C.rejectBuffer l a = C.sourceForm l '' C.primarySet (C.connectionSource l) a := by
  classical
  rw [C.source_truth_image]
  unfold rejectBuffer
  split
  · simp
  · exact BufferAlgebra.correlated_projection (C.rejectDestination_nonempty l a) j

theorem rejectBuffer_sum (h : ¬ C.Accepted) (l : C.Connection) (a : (C.connectionMap l).Point) :
    (fun v => v 0 + v 1) '' C.rejectBuffer l ((C.connectionMap l).source a) =
      (fun v => C.rejectConstant (.third l) + C.targetForm l v) ''
        C.primarySet (C.connectionTarget l) ((C.connectionMap l).target a) := by
  classical
  change _ = C.rejectDestination l ((C.connectionMap l).source a)
  unfold rejectBuffer
  split
  · rw [C.rejectDestination_true h l a ‹_›]
    simp
  · exact BufferAlgebra.correlated_sum _

/-- Rejection produces actual nonempty scalar-image sets, including correlated
buffers. This does not assert an unavailable simultaneous global assignment. -/
noncomputable def rejectingImages (h : ¬ C.Accepted) : C.schemas.SpecialImages C.rejectConstant where
  values p a := match p with
    | .primary p => C.primarySet p a
    | .buffer l => C.rejectBuffer l a
    | .dummy => Set.univ
  nonempty p a := by
    cases p with
    | primary p => exact BufferAlgebra.truthVectors_nonempty _
    | buffer l => exact C.rejectBuffer_nonempty l a
    | dummy => exact ⟨0, Set.mem_univ _⟩
  equation e a := by
    classical
    cases e with
    | seed z =>
      change sumForm (C.dimension (C.seedType z)) '' C.primarySet (some (C.seedType z))
        ((C.seedMap z).source a) = (fun _ : Fin 1 → Bit => (0 : Bit)) '' Set.univ
      have ht : C.True (C.seedType z) ((C.seedMap z).source a) := fun j => PortTrue.seed z a j
      have hs := BufferAlgebra.sum_truth (C.PortTrue (C.seedType z) ((C.seedMap z).source a))
      rw [ite_eq_left (show ∀ j, C.PortTrue (C.seedType z) ((C.seedMap z).source a) j from ht)] at hs
      rw [show ⇑(sumForm (C.dimension (C.seedType z))) = (fun v => ∑ j, v j) from funext (sumForm_apply _)]
      simpa using hs
    | first l =>
      change C.sourceForm l '' C.primarySet (C.connectionSource l) ((C.connectionMap l).source a) =
        (fun v : Fin 2 → Bit => 0 + v 0) '' C.rejectBuffer l ((C.connectionMap l).source a)
      simpa only [zero_add] using (C.rejectBuffer_projection l ((C.connectionMap l).source a) 0).symm
    | second l =>
      change C.sourceForm l '' C.primarySet (C.connectionSource l) ((C.connectionMap l).source a) =
        (fun v : Fin 2 → Bit => 0 + v 1) '' C.rejectBuffer l ((C.connectionMap l).source a)
      simpa only [zero_add] using (C.rejectBuffer_projection l ((C.connectionMap l).source a) 1).symm
    | third l => exact C.rejectBuffer_sum h l a

end ProductCircuit

namespace Marker

theorem sum_delta {r : ℕ} (hr : 0 < r) : ∑ i : Fin r, delta i = 1 := by
  cases r with
  | zero => omega
  | succ n =>
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [delta]
    · intro i _ hi
      have hn : i.val + 1 ≠ n + 1 := by
        intro he
        exact hi (Fin.ext (Nat.add_right_cancel he))
      exact ite_eq_right hn
    · simp

end Marker

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem linkShift_special (hr : 0 < r) (n : ℕ) (b : E → Bit) (l : S.Link n)
    (a : (S.layout n).MatchAddress l) :
    (S.layout n).linkShift (S.specialTwist n b) l a = S.linkConstant n b l := by
  dsimp only [RingLayout.linkShift, specialTwist]
  rw [← Finset.sum_mul, Marker.sum_delta hr, one_mul]

theorem wireShift_special (hr : 0 < r) (n : ℕ) (b : E → Bit) (e : E)
    (a : S.DomainAddress e) : S.wireShift n (S.specialTwist n b) e a = b e := by
  dsimp only [wireShift, firstShift, middleShift, lastShift, RingLayout.linkShift,
    specialTwist, linkConstant]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_mul, Marker.sum_delta hr, one_mul]

end ComparisonSchemas

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

theorem special_not_isomorphic (hr : 32 ≤ r) (n : ℕ) :
    ¬ Isomorphic (((C.schemas.layout n).affine (by omega)).graph 0)
      (((C.schemas.layout n).affine (by omega)).graph (C.schemas.specialTwist n C.rejectConstant)) := by
  intro hi
  obtain ⟨h, _, he⟩ := (C.schemas.offsets_iff_real_rowSums (by omega) n _).mp
    ((((C.schemas.layout n).affine (by omega)).graph_isomorphic_iff _).mp hi)
  have hc (e : C.Comparison) (a : (C.comparisonMap e).Point) := he e a
  have hc' (e : C.Comparison) (a : (C.comparisonMap e).Point) :
      C.schemas.left e (h (C.schemas.source e) (C.schemas.sourceAddress e a)) +
        C.schemas.right e (h (C.schemas.target e) (C.schemas.targetAddress e a)) = C.rejectConstant e :=
    (hc e a).trans (C.schemas.wireShift_special (by omega) n C.rejectConstant e a)
  let a := ProductMap.ofAddress (fun _ : Fin r => false)
  have h₁ := hc' (.first (.self none 0)) a
  have h₂ := hc' (.second (.self none 0)) a
  have h₃ := hc' (.third (.self none 0)) a
  have g₁ := hc' (.first .conflict) a
  have g₂ := hc' (.second .conflict) a
  have g₃ := hc' (.third .conflict) a
  let x := h (.primary none) a (0 : Fin 1)
  let z : Fin 2 → Bit := h (.buffer (.self none 0)) a
  let v : Fin 2 → Bit := h (.buffer .conflict) a
  change x + z 0 = 0 at h₁
  change x + z 1 = 0 at h₂
  change (z 0 + z 1) + x = 0 at h₃
  change x + v 0 = 0 at g₁
  change x + v 1 = 0 at g₂
  change (v 0 + v 1) + x = 1 at g₃
  rw [← CharTwo.add_eq_zero.mp h₁, ← CharTwo.add_eq_zero.mp h₂,
    CharTwo.add_self_eq_zero, zero_add] at h₃
  rw [← CharTwo.add_eq_zero.mp g₁, ← CharTwo.add_eq_zero.mp g₂,
    CharTwo.add_self_eq_zero, zero_add] at g₃
  exact zero_ne_one (h₃.symm.trans g₃)

/-- Rejection prevents identification for the full least-closure product
circuit, not only for a promised selection of comparison mates. -/
theorem not_identifies_of_rejected (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n)
    (h : ¬ C.Accepted) : ¬ Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) := by
  intro hi
  exact C.special_not_isomorphic hr n
    (hi _ ((C.rejectingImages h).equivalent_special hr hn))

theorem identifies_iff_accepted (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n) :
    Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) ↔ C.Accepted := by
  constructor
  · intro hi
    by_contra hnacc
    exact C.not_identifies_of_rejected hr n hn hnacc hi
  · exact C.identifies_of_accepted hr n

end ProductCircuit

/-- Retained color history always determines the original atomic type. -/
theorem tupleColor_zero_eq {G H : Graph} {k s : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) :
    tupleColor G k 0 v = tupleColor H k 0 w := by
  induction s with
  | zero => exact h
  | succ s ih => exact ih (congrArg Prod.fst h)

theorem tupleColor_atomic {G H : Graph} {k s : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) := by
  have h0 := tupleColor_zero_eq h
  exact ⟨fun i j => decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst h0) i) j),
    fun i j => congrFun (congrFun (congrArg Prod.snd h0) i) j⟩

/-- Restricting a joint color retains an entire replacement vector at once. -/
def restrictTupleColor {j k : ℕ} (q : Fin j → Fin k) :
    (s : ℕ) → TupleColor k s → TupleColor j s
  | 0, c => (fun i l => c.1 (q i) (q l), fun i l => c.2 (q i) (q l))
  | s + 1, c => (restrictTupleColor q s c.1,
      c.2.map (fun v i => restrictTupleColor q s (v (q i))))

theorem restrictTupleColor_apply (G : Graph) {j k : ℕ} (q : Fin j → Fin k)
    (hq : Function.Injective q) (s : ℕ) (v : Fin k → Fin G.order) :
    restrictTupleColor q s (tupleColor G k s v) = tupleColor G j s (v ∘ q) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    dsimp only [restrictTupleColor, tupleColor]
    apply Prod.ext (ih v)
    dsimp only [Prod.snd]
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    dsimp only [Function.comp_def]
    rw [ih, Function.update_comp_eq_of_injective v hq]
    rfl

def padIndex {j k : ℕ} (hj : 0 < j) (_hjk : j ≤ k) (i : Fin k) : Fin j :=
  if hi : i.val < j then ⟨i.val, hi⟩ else ⟨0, hj⟩

@[simp] theorem padIndex_castLE {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (i : Fin j) :
    padIndex hj hjk (Fin.castLE hjk i) = i := by
  simp [padIndex, i.isLt]

def paddedEquiv {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (α : Type) :
    (Fin j → α) ≃ {v : Fin k → α // ∀ i, v i = v (Fin.castLE hjk (padIndex hj hjk i))} where
  toFun v := ⟨v ∘ padIndex hj hjk, fun i => by simp⟩
  invFun v := v.val ∘ Fin.castLE hjk
  left_inv v := by funext i; simp
  right_inv v := by
    apply Subtype.ext
    funext i
    exact (v.property i).symm

theorem tupleHistogram_dimension_mono {G H : Graph} {j k s : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : tupleHistogram G k s = tupleHistogram H k s) :
    tupleHistogram G j s = tupleHistogram H j s := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  have hp (v : Fin k → Fin G.order) :
      (∀ i, v i = v (Fin.castLE hjk (padIndex hj hjk i))) ↔
      (∀ i, E v i = E v (Fin.castLE hjk (padIndex hj hjk i))) :=
    forall_congr' (fun i => (tupleColor_atomic (hE v)).1 i _)
  let e := (paddedEquiv hj hjk (Fin G.order)).trans
    ((E.subtypeEquiv hp).trans (paddedEquiv hj hjk (Fin H.order)).symm)
  apply histogram_eq_of_equiv e
  intro v
  have hh := congrArg (restrictTupleColor (Fin.castLE hjk) s) (hE (v ∘ padIndex hj hjk))
  rw [restrictTupleColor_apply _ _ (Fin.castLE_injective _),
    restrictTupleColor_apply _ _ (Fin.castLE_injective _)] at hh
  have hv : (v ∘ padIndex hj hjk) ∘ Fin.castLE hjk = v := by funext i; simp
  rw [hv] at hh
  exact hh

/-- Ordinary neighbor refinement is recoverable from any joint dimension >=2. -/
theorem neighborColor_of_tupleColor {G H : Graph} {k : ℕ} (hk : 2 ≤ k) (s : ℕ)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) (i : Fin k) :
    neighborColor G s (v i) = neighborColor H s (w i) := by
  induction s generalizing v w i with
  | zero => rfl
  | succ s ih =>
    have hprev := congrArg Prod.fst h
    obtain ⟨e, he⟩ := exists_colorEquiv
      (fun z i => tupleColor G k s (Function.update v i z))
      (fun z i => tupleColor H k s (Function.update w i z)) (congrArg Prod.snd h)
    obtain ⟨j, hij⟩ : ∃ j : Fin k, i ≠ j := by
      by_cases hi : i = ⟨0, by omega⟩
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [hi]
        intro he
        have := congrArg Fin.val he
        change (0 : ℕ) = 1 at this
        omega
      · exact ⟨⟨0, by omega⟩, hi⟩
    change (neighborColor G s (v i), _) = (neighborColor H s (w i), _)
    apply Prod.ext (ih hprev i)
    apply filteredHistogram_eq_of_equiv e
    · intro z
      have hz := (tupleColor_atomic (congrFun (he z) j)).2 i j
      simp only [Function.update_of_ne hij, Function.update_self] at hz
      rw [hz]
    · intro z
      simpa only [Function.update_self] using ih (congrFun (he z) j) j

theorem neighborHistogram_of_tupleHistogram {G H : Graph} {k s : ℕ} (hk : 2 ≤ k)
    (h : tupleHistogram G k s = tupleHistogram H k s) :
    neighborHistogram G s = neighborHistogram H s := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  let i : Fin k := ⟨0, by omega⟩
  have hp (v : Fin k → Fin G.order) :
      (∀ j, v j = v i) ↔ ∀ j, E v j = E v i :=
    forall_congr' (fun j => (tupleColor_atomic (hE v)).1 j i)
  let e := (diagonalEquiv i (Fin G.order)).trans
    ((E.subtypeEquiv hp).trans (diagonalEquiv i (Fin H.order)).symm)
  exact histogram_eq_of_equiv e _ _ (fun v => neighborColor_of_tupleColor hk s (hE (fun _ => v)) i)

theorem equivalent_dimension_mono {G H : Graph} {j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : Equivalent k G H) : Equivalent j G H := by
  by_cases he : j = k
  · simpa only [he] using h
  have hk : 2 ≤ k := by omega
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  unfold Equivalent
  split_ifs with hj1
  · intro s; exact neighborHistogram_of_tupleHistogram hk (h s)
  · intro s; exact tupleHistogram_dimension_mono hj hjk (h s)

theorem identifies_dimension_mono {G : Graph} {j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : Identifies j G) : Identifies k G :=
  fun H hH => h H (equivalent_dimension_mono hj hjk hH)

/-- A finite graph has a positive identifying dimension without any restriction
on the order of its candidate mate. -/
theorem identifies_order (G : Graph) : Identifies (max 2 G.order) G := by
  intro H he
  obtain ⟨e, _⟩ := equivalent_degreeBijection (le_max_left _ _) he
  by_cases hn : 0 < G.order
  · obtain ⟨f, hf, ha, _⟩ := equivalent_local_match (le_max_left _ _) he
      (le_max_right _ _) hn (fun i => i)
    have hfi : Function.Injective f := fun i j h => (hf i j).mpr h
    have hfb : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, Fintype.card_congr e⟩
    exact ⟨Equiv.ofBijective f hfb, ha⟩
  · exact ⟨e, fun u _ => by have := u.isLt; omega⟩

theorem positive_identifying_nonempty (G : Graph) :
    {k : ℕ | 0 < k ∧ Identifies k G}.Nonempty :=
  ⟨max 2 G.order, by have := le_max_left 2 G.order; omega, identifies_order G⟩

theorem WLdim_spec (G : Graph) : 0 < WLdim G ∧ Identifies (WLdim G) G :=
  Nat.sInf_mem (positive_identifying_nonempty G)

theorem WLdim_le_iff {G : Graph} {k : ℕ} (hk : 0 < k) : WLdim G ≤ k ↔ Identifies k G := by
  constructor
  · intro h; exact identifies_dimension_mono (WLdim_spec G).1 h (WLdim_spec G).2
  · intro h; exact Nat.sInf_le ⟨hk, h⟩

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

theorem dimension_iff_accepted (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n) :
    WLdim (((C.schemas.layout n).affine (by omega)).graph 0) ≤ r ↔ C.Accepted := by
  rw [WLdim_le_iff (by omega), C.identifies_iff_accepted hr n hn]

end ProductCircuit

end WLIdentification

end OAI
