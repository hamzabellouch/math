import OAI.Combinatorics.ParityLifts.Model

namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)


noncomputable def liftProjection (τ : G →g T) (b : A → Bit) :
    liftGraph T G τ b →g G where
  toFun := Sigma.fst
  map_rel' := fun h => h.1

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

abbrev Variables := (x : W) → T.neighborSet (τ (φ x)) → Bit

noncomputable instance variablesFintype : Fintype (Variables T G F τ φ) := by
  classical
  unfold Variables
  infer_instance

noncomputable def LiftEquations (b : A → Bit) (z : Variables T G F τ φ) : Prop :=
  (∀ x, ∑ v, z x v = b (τ (φ x))) ∧
  (∀ x y (h : F.Adj x y),
    z x ⟨τ (φ y), τ.map_adj (φ.map_adj h)⟩ =
      z y ⟨τ (φ x), τ.map_adj (φ.map_adj h.symm)⟩)

noncomputable def Solutions (b : A → Bit) :=
  {z : Variables T G F τ φ // LiftEquations T G F τ φ b z}

noncomputable instance solutionsFintype (b : A → Bit) :
    Fintype (Solutions T G F τ φ b) := by
  classical
  unfold Solutions
  infer_instance

noncomputable def zeroSolution : Solutions T G F τ φ (fun _ => 0) :=
  ⟨fun _ _ => 0, by classical simp [LiftEquations]⟩

noncomputable def solutionHom (b : A → Bit) (z : Solutions T G F τ φ b) :
    F →g liftGraph T G τ b where
  toFun x := ⟨φ x, ⟨z.1 x, z.2.1 x⟩⟩
  map_rel' := by
    intro x y h
    exact ⟨φ.map_adj h, z.2.2 x y h⟩

noncomputable def homSolutionsEquiv (b : A → Bit) :
    (F →g liftGraph T G τ b) ≃ ((φ : F →g G) × Solutions T G F τ φ b) where
  toFun f := ⟨(liftProjection T G τ b).comp f,
    ⟨fun x => (f x).2.1,
      ⟨fun x => (f x).2.2, fun x y h => (f.map_adj h).2⟩⟩⟩
  invFun p := solutionHom T G F τ p.1 b p.2
  left_inv f := by
    apply RelHom.ext
    intro x
    rfl
  right_inv p := by
    rcases p with ⟨φ, z, hz⟩
    rfl

noncomputable def homogeneousTranslate (b : A → Bit) (v : Solutions T G F τ φ b) :
    Solutions T G F τ φ b ≃ Solutions T G F τ φ (fun _ => 0) where
  toFun z := ⟨z.1 - v.1, by
    classical
    constructor
    · intro x
      change ∑ w, (z.1 x w - v.1 x w) = 0
      rw [Finset.sum_sub_distrib, z.2.1 x, v.2.1 x, sub_self]
    · intro x y h
      change z.1 x _ - v.1 x _ = z.1 y _ - v.1 y _
      rw [z.2.2 x y h, v.2.2 x y h]⟩
  invFun z := ⟨z.1 + v.1, by
    classical
    constructor
    · intro x
      change ∑ w, (z.1 x w + v.1 x w) = b (τ (φ x))
      rw [Finset.sum_add_distrib, z.2.1 x, v.2.1 x, zero_add]
    · intro x y h
      change z.1 x _ + v.1 x _ = z.1 y _ + v.1 y _
      rw [z.2.2 x y h, v.2.2 x y h]⟩
  left_inv z := by
    apply Subtype.ext
    exact sub_add_cancel z.1 v.1
  right_inv z := by
    apply Subtype.ext
    exact add_sub_cancel_right z.1 v.1

omit [Fintype V] in
lemma solutions_card_eq_of_nonempty (b : A → Bit)
    (h : Nonempty (Solutions T G F τ φ b)) :
    Fintype.card (Solutions T G F τ φ b) =
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  obtain ⟨v⟩ := h
  exact Fintype.card_congr (homogeneousTranslate T G F τ φ b v)

omit [Fintype V] in
lemma solutions_card_le (b : A → Bit) :
    Fintype.card (Solutions T G F τ φ b) ≤
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  classical
  by_cases h : Nonempty (Solutions T G F τ φ b)
  · exact (solutions_card_eq_of_nonempty T G F τ φ b h).le
  · have : IsEmpty (Solutions T G F τ φ b) := not_nonempty_iff.mp h
    simp

omit [Fintype V] in
lemma solutions_card_eq_iff (b : A → Bit) :
    Fintype.card (Solutions T G F τ φ b) =
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) ↔
      Nonempty (Solutions T G F τ φ b) := by
  constructor
  · intro h
    have : Nonempty (Solutions T G F τ φ (fun _ => 0)) :=
      ⟨zeroSolution T G F τ φ⟩
    apply Fintype.card_pos_iff.mp
    rw [h]
    exact Fintype.card_pos
  · exact solutions_card_eq_of_nonempty T G F τ φ b

noncomputable def homCount {U : Type} [Fintype U] (H : SimpleGraph U) : ℕ := by
  classical
  exact Fintype.card (F →g H)

lemma homCount_lift (b : A → Bit) :
    homCount F (liftGraph T G τ b) =
      ∑ φ : F →g G, Fintype.card (Solutions T G F τ φ b) := by
  classical
  unfold homCount
  rw [Fintype.card_congr (homSolutionsEquiv T G F τ b), Fintype.card_sigma]

/-- Noncancellation for every uncolored homomorphism, not just typed witnesses. -/
theorem homCount_lift_le (b : A → Bit) :
    homCount F (liftGraph T G τ b) ≤ homCount F (liftGraph T G τ (fun _ => 0)) := by
  classical
  rw [homCount_lift T G F τ b, homCount_lift T G F τ (fun _ => 0)]
  exact Finset.sum_le_sum (fun φ _ => solutions_card_le T G F τ φ b)


lemma homCount_lift_eq_iff (b : A → Bit) :
    homCount F (liftGraph T G τ b) = homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∀ φ : F →g G, Nonempty (Solutions T G F τ φ b) := by
  classical
  rw [homCount_lift T G F τ b, homCount_lift T G F τ (fun _ => 0),
    Finset.sum_eq_sum_iff_of_le (fun φ _ => solutions_card_le T G F τ φ b)]
  simp only [Finset.mem_univ, forall_const, solutions_card_eq_iff]

/-- A strict uncolored count gap comes from an inconsistent projected system. -/
theorem homCount_lift_strict_iff (b : A → Bit) :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, ¬ Nonempty (Solutions T G F τ φ b) := by
  have hle := homCount_lift_le T G F τ b
  have heq := homCount_lift_eq_iff T G F τ b
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have := heq.mpr hn
    omega
  · rintro ⟨φ, hφ⟩
    have hn : homCount F (liftGraph T G τ b) ≠
        homCount F (liftGraph T G τ (fun _ => 0)) := fun h => hφ (heq.mp h φ)
    omega

abbrev EquationRow := W ⊕ F.Dart

noncomputable def constraintMap :
    Variables T G F τ φ →ₗ[Bit] (EquationRow F → Bit) where
  toFun z := fun row => match row with
    | .inl x => ∑ v, z x v
    | .inr d =>
      z d.fst ⟨τ (φ d.snd), τ.map_adj (φ.map_adj d.adj)⟩ +
        z d.snd ⟨τ (φ d.fst), τ.map_adj (φ.map_adj d.adj.symm)⟩
  map_add' z w := by
    funext row
    cases row with
    | inl x => exact Finset.sum_add_distrib
    | inr d => dsimp; ring
  map_smul' a z := by
    funext row
    cases row with
    | inl x =>
      change (∑ v, a * z x v) = a * ∑ v, z x v
      exact (Finset.mul_sum ..).symm
    | inr d => dsimp; ring

noncomputable def constraintRHS (b : A → Bit) : EquationRow F → Bit
  | .inl x => b (τ (φ x))
  | .inr _ => 0

omit [Fintype V] [Fintype W] in
lemma liftEquations_iff (b : A → Bit) (z : Variables T G F τ φ) :
    LiftEquations T G F τ φ b z ↔
      constraintMap T G F τ φ z = constraintRHS T G F τ φ b := by
  constructor
  · rintro ⟨hvertex, hedge⟩
    funext row
    cases row with
    | inl x => exact hvertex x
    | inr d =>
      change z d.fst _ + z d.snd _ = 0
      rw [hedge d.fst d.snd d.adj, CharTwo.add_self_eq_zero]
  · intro h
    constructor
    · intro x
      exact congrFun h (.inl x)
    · intro x y hxy
      have he := congrFun h (.inr ⟨(x, y), hxy⟩)
      change z x _ + z y _ = 0 at he
      rwa [← CharTwo.sub_eq_add, sub_eq_zero] at he

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

lemma bit_zero_or_one (b : Bit) : b = 0 ∨ b = 1 := by
  have h : ∀ b : Bit, b = 0 ∨ b = 1 := by decide
  exact h b

/-- Linear-algebra separation without a rank assumption. -/
theorem binary_alternative (L : E →ₗ[Bit] H) (c : H) :
    (¬ ∃ z, L z = c) ↔
      ∃ f : H →ₗ[Bit] Bit, (∀ z, f (L z) = 0) ∧ f c = 1 := by
  classical
  constructor
  · intro h
    have hc : c ∉ LinearMap.range L := h
    obtain ⟨f, hf, hmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
    refine ⟨f, ?_, ?_⟩
    · intro z
      have hz : f (L z) ∈ (LinearMap.range L).map f :=
        ⟨L z, ⟨z, rfl⟩, rfl⟩
      rwa [hmap, Submodule.mem_bot] at hz
    · exact (bit_zero_or_one (f c)).resolve_left hf
  · rintro ⟨f, hf, hc⟩ ⟨z, hz⟩
    have h := hf z
    rw [hz, hc] at h
    exact one_ne_zero h

end BinaryDuality

end ParityWL

end OAI
