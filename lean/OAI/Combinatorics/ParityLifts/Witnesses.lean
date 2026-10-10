import OAI.Combinatorics.ParityLifts.DecompositionCuts

namespace OAI

namespace ParityWL

open scoped BigOperators

section WitnessConverse

open scoped Classical

variable {A W : Type} [Fintype A] [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

omit [Fintype A] in
lemma WeightedWitness.coordinate_neighbors (w : WeightedWitness T F a b)
    (x : W) (u : T.neighborSet (a x)) :
    (∑ y : F.neighborSet x, if a y = u.1 then w.edge x y else 0) = w.vertex x := by
  change (∑ y : {y // F.Adj x y}, if a y.1 = u.1 then w.edge x y.1 else 0) = _
  rw [sum_subtype_indicator (F.Adj x)
    (fun y => if a y = u.1 then w.edge x y else 0)]
  convert w.coordinate x u using 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : F.Adj x y
  · simp [h]
  · simp [h, w.supported x y h]

lemma WeightedWitness.tag_sum (w : WeightedWitness T F a b)
    (z : (x : W) → T.neighborSet (a x) → Bit) :
    (∑ x, w.vertex x * ∑ u, z x u) =
      ∑ d : F.Dart, w.edge d.fst d.snd * z d.fst ⟨a d.snd, a.map_adj d.adj⟩ := by
  have hx : ∀ x, w.vertex x * ∑ u, z x u =
      ∑ y : F.neighborSet x, w.edge x y * z x ⟨a y, a.map_adj y.2⟩ := by
    intro x
    rw [Finset.mul_sum]
    calc
      _ = ∑ u : T.neighborSet (a x),
          (∑ y : F.neighborSet x, if a y = u.1 then w.edge x y else 0) * z x u := by
        simp_rw [w.coordinate_neighbors]
      _ = ∑ y : F.neighborSet x, ∑ u : T.neighborSet (a x),
          if a y = u.1 then w.edge x y * z x u else 0 := by
        simp_rw [Finset.sum_mul, ite_mul, zero_mul]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        have he : ∀ u : T.neighborSet (a x),
            a y = u.1 ↔ u = ⟨a y, a.map_adj y.2⟩ := by
          intro u
          constructor
          · intro h; exact Subtype.ext h.symm
          · intro h; exact (congrArg Subtype.val h).symm
        simp [he]
  rw [Fintype.sum_congr _ _ hx]
  calc
    _ = ∑ d : (x : W) × F.neighborSet x,
        w.edge d.1 d.2 * z d.1 ⟨a d.2, a.map_adj d.2.2⟩ :=
      (Fintype.sum_sigma _).symm
    _ = _ := (Equiv.sum_comp (dartNeighborsEquiv F)
      (fun d : (x : W) × F.neighborSet x =>
        w.edge d.1 d.2 * z d.1 ⟨a d.2, a.map_adj d.2.2⟩)).symm

/-- A genuine dual certificate makes the source-indexed tag system inconsistent. -/
theorem WeightedWitness.no_tags (w : WeightedWitness T F a b)
    (z : (x : W) → T.neighborSet (a x) → Bit)
    (hz : ∀ x, ∑ u, z x u = b (a x))
    (he : ∀ x y (h : F.Adj x y),
      z x ⟨a y, a.map_adj h⟩ = z y ⟨a x, a.map_adj h.symm⟩) : False := by
  have h := w.tag_sum z
  simp_rw [hz] at h
  rw [w.odd] at h
  have hzero : (∑ d : F.Dart, w.edge d.fst d.snd *
      z d.fst ⟨a d.snd, a.map_adj d.adj⟩) = 0 := by
    apply Finset.sum_ninvolution SimpleGraph.Dart.symm
    · intro d
      change w.edge d.fst d.snd * z d.fst _ + w.edge d.snd d.fst * z d.snd _ = 0
      rw [w.symmetric d.fst d.snd, he d.fst d.snd d.adj]
      exact CharTwo.add_self_eq_zero _
    · intro d _
      exact d.symm_ne
    · simp
    · exact SimpleGraph.Dart.symm_symm
  exact one_ne_zero (h.trans hzero)

variable {V : Type} [Fintype V] {G : SimpleGraph V} {τ : G →g T} {φ : F →g G}

omit [Fintype V] in
theorem weightedWitness_inconsistent
    (w : WeightedWitness T F (τ.comp φ) b) :
    ¬ Nonempty (Solutions T G F τ φ b) := by
  rintro ⟨z⟩
  exact w.no_tags z.1 z.2.1 z.2.2

theorem homCount_lift_strict_iff_witness :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, Nonempty (WeightedWitness T F (τ.comp φ) b) := by
  rw [homCount_lift_strict_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, inconsistent_weightedWitness T G F τ φ b hφ⟩
  · rintro ⟨φ, ⟨w⟩⟩
    exact ⟨φ, weightedWitness_inconsistent w⟩

end WitnessConverse

section PositiveWitness

open scoped Classical

variable {t : ℕ} {C : ChoiceSystem t}

lemma BaseArc.type_adj {x y : BaseVertex C} (h : BaseArc C x y) :
    (template t).Adj (baseType x) (baseType y) := by
  cases h with
  | main p d e he => exact ne_of_lt p.property
  | left h d => exact Or.inl rfl
  | right h e => exact Or.inr (Or.inl rfl)
  | third h q d => exact Or.inr (Or.inr rfl)

lemma BaseArc.adj {x y : BaseVertex C} (h : BaseArc C x y) :
    (baseGraph C).Adj x y := by
  refine ⟨?_, Or.inl h⟩
  intro he
  exact (template t).ne_of_adj h.type_adj (congrArg baseType he)

noncomputable def choiceMap (d : (i : Fin t) → C.Domain i)
    (hd : ∀ p : MainPair t, C.leftLabel p (d p.1.1) = C.rightLabel p (d p.1.2)) :
    template t →g baseGraph C where
  toFun
    | .inl i => .inl ⟨i, d i⟩
    | .inr h => .inr ⟨h, C.leftLabel h.1.1 (d h.1.1.1.1)⟩
  map_rel' := by
    have help : ∀ h i, helperIncident h i → (baseGraph C).Adj
        (.inr ⟨h, C.leftLabel h.1.1 (d h.1.1.1.1)⟩) (.inl ⟨i, d i⟩) := by
      intro h i hi
      rcases hi with rfl | rfl | rfl
      · exact (BaseArc.left h _).adj
      · rw [hd h.1.1]
        exact (BaseArc.right h _).adj
      · exact (BaseArc.third h _ _).adj
    intro x y he
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        rcases lt_or_gt_of_ne he with hij | hji
        · exact (BaseArc.main ⟨(i,j), hij⟩ (d i) (d j) (hd _)).adj
        · exact (BaseArc.main ⟨(j,i), hji⟩ (d j) (d i) (hd _)).adj.symm
      | inr h => exact (help h i he).symm
    | inr h =>
      cases y with
      | inl i => exact help h i he
      | inr g => exact False.elim he

@[simp] lemma choiceMap_type (d : (i : Fin t) → C.Domain i)
    (hd : ∀ p : MainPair t, C.leftLabel p (d p.1.1) = C.rightLabel p (d p.1.2))
    (v : TemplateVertex t) : baseType (choiceMap d hd v) = v := by
  cases v <;> rfl

/-- The explicit noncancelling source is the uncolored template itself. -/
theorem successful_template_count_gap (ht : 0 < t) (hs : C.Successful) :
    homCount (template t) (starLift C) < homCount (template t) (zeroLift C) := by
  obtain ⟨d, hd⟩ := hs
  let φ := choiceMap d hd
  have hφ : ∀ v, ((baseProjection C).comp φ) v = v := choiceMap_type d hd
  apply homCount_lift_strict_iff_witness.mpr
  refine ⟨φ, ⟨{
    vertex := fun _ => 1
    edge := fun x y => if (template t).Adj x y then 1 else 0
    symmetric := by intro x y; simp [SimpleGraph.adj_comm]
    supported := by intro x y h; simp [h]
    coordinate := ?_
    odd := ?_ }⟩⟩
  · intro x u
    simp only [hφ]
    have hu : (template t).Adj x u.1 := by simpa [hφ] using u.2
    simp [hu]
  · simp only [one_mul, hφ]
    simp [starParity_value ht]

end PositiveWitness

end ParityWL

end OAI
