import OAI.Analysis.SeparableQuotients.PrefixNormers

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance selectionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance selectionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

/-- Finite half-normers in the unit ball. -/
theorem exists_finite_normers (F : Submodule 𝕜 (StrongDual 𝕜 X))
    [FiniteDimensional 𝕜 F] :
    ∃ D : Finset X, (∀ d ∈ D, ‖d‖ ≤ 1) ∧
      ∀ v : F, ∃ d ∈ D, ‖v‖ ≤ 2 * ‖(v : StrongDual 𝕜 X) d‖ := by
  classical
  let U (d : closedBall (0 : X) 1) : Set F :=
    {v | (1 / 2 : ℝ) < ‖(v : StrongDual 𝕜 X) d‖}
  have hU : ∀ d, IsOpen (U d) := by
    intro d
    exact isOpen_lt continuous_const
      (((NormedSpace.inclusionInDoubleDual 𝕜 X d).comp F.subtypeL).continuous.norm)
  have hcover : sphere (0 : F) 1 ⊆ ⋃ d, U d := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
    obtain ⟨d, hd, he⟩ := (v : StrongDual 𝕜 X).exists_lt_apply_of_lt_opNorm
      (by change (1 / 2 : ℝ) < ‖v‖; rw [hn]; norm_num)
    exact Set.mem_iUnion.mpr ⟨⟨d, by simpa only [mem_closedBall, dist_zero_right] using hd.le⟩, he⟩
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U hU hcover
  refine ⟨insert 0 (t.image Subtype.val), ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
      simpa only [mem_closedBall, dist_zero_right] using e.property
  · intro v
    by_cases hv : v = 0
    · subst v; exact ⟨0, Finset.mem_insert_self _ _, by simp⟩
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : F := (↑‖v‖ : 𝕜)⁻¹ • v
    have hw : w ∈ sphere (0 : F) 1 := by
      simp only [w, mem_sphere, dist_zero_right, norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
    obtain ⟨d, hd, he⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨d, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, hd, rfl⟩), ?_⟩
    change (1 / 2 : ℝ) < ‖((↑‖v‖ : 𝕜)⁻¹ • (v : StrongDual 𝕜 X)) d‖ at he
    simp only [smul_apply, norm_smul, norm_inv,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v)] at he
    have hm := (mul_lt_mul_of_pos_left he hp)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at hm
    linarith

/-- Finite annihilation conditions leave a unit functional in every infinite-dimensional
subspace. -/
theorem exists_unit_annihilator (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (A : Finset X) :
    ∃ f : F, ‖f‖ = 1 ∧ ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0 := by
  classical
  let T : F →ₗ[𝕜] (A → 𝕜) :=
    { toFun := fun f x => (f : StrongDual 𝕜 X) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hex : ∃ f : F, f ≠ 0 ∧ ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0 := by
    by_contra! hn
    apply hF (FiniteDimensional.of_injective T ?_)
    intro a b hab
    apply sub_eq_zero.mp
    by_contra h
    obtain ⟨x, hx, hne⟩ := hn (a - b) h
    apply hne
    have he := congrFun hab ⟨x, hx⟩
    exact sub_eq_zero.mpr he
  obtain ⟨f, hf, hzero⟩ := hex
  refine ⟨(↑‖f‖ : 𝕜)⁻¹ • f, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg f), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hf)]
  · intro x hx
    simp [hzero x hx]

/-- One finite stage of the normer construction. -/
structure NormerStep (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (A : Finset X) (S : Finset (StrongDual 𝕜 X)) where
  f : F
  D : Finset X
  norm_f : ‖f‖ = 1
  vanish : ∀ x ∈ A, (f : StrongDual 𝕜 X) x = 0
  unit : ∀ d ∈ D, ‖d‖ ≤ 1
  norming : ∀ v ∈ Submodule.span 𝕜 (insert (f : StrongDual 𝕜 X) (S : Set _)),
    ∃ d ∈ D, ‖v‖ ≤ 2 * ‖v d‖

noncomputable def chooseNormerStep (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hF : ¬ FiniteDimensional 𝕜 F) (A : Finset X) (S : Finset (StrongDual 𝕜 X)) :
    NormerStep F A S := Classical.choice <| by
  classical
  obtain ⟨f, hf, hv⟩ := exists_unit_annihilator F hF A
  let G := Submodule.span 𝕜 (insert (f : StrongDual 𝕜 X) (S : Set _))
  let : FiniteDimensional 𝕜 G := FiniteDimensional.span_of_finite 𝕜 (S.finite_toSet.insert _)
  obtain ⟨D, hD, hn⟩ := exists_finite_normers G
  exact ⟨⟨f, D, hf, hv, hD, fun v hv => hn ⟨v, hv⟩⟩⟩

namespace NormerStep
noncomputable local instance : DecidableEq X := Classical.decEq X
noncomputable local instance : DecidableEq (StrongDual 𝕜 X) := Classical.decEq _
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

/-- Accumulated annihilation constraints and preceding functionals. -/
noncomputable def state : ℕ → Finset X × Finset (StrongDual 𝕜 X)
  | 0 => (∅, ∅)
  | n + 1 =>
    let p := state n
    let q := chooseNormerStep F hF (insert (xs n) p.1) p.2
    (insert (xs n) (p.1 ∪ q.D), insert (q.f : StrongDual 𝕜 X) p.2)

noncomputable def stage (n : ℕ) :=
  chooseNormerStep F hF (insert (xs n) (state F hF xs n).1) (state F hF xs n).2

noncomputable def seq (n : ℕ) : StrongDual 𝕜 X := (stage F hF xs n).f

lemma state_succ (n : ℕ) :
    state F hF xs (n + 1) =
      (insert (xs n) ((state F hF xs n).1 ∪ (stage F hF xs n).D),
       insert (seq F hF xs n) (state F hF xs n).2) := rfl

lemma state_monotone : Monotone (fun n => (state F hF xs n).1) := by
  classical
  apply monotone_nat_of_le_succ
  intro n d hd
  rw [state_succ]
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hd)

lemma state_vectors (n : ℕ) :
    (state F hF xs n).2 = (Finset.range n).image (seq F hF xs) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => simp only [state_succ, Finset.range_add_one, Finset.image_insert, ih]

lemma seq_mem (n : ℕ) : seq F hF xs n ∈ F := (stage F hF xs n).f.property
lemma seq_norm (n : ℕ) : ‖seq F hF xs n‖ = 1 := (stage F hF xs n).norm_f

lemma seq_vanish_x {m n : ℕ} (hmn : m ≤ n) : seq F hF xs n (xs m) = 0 := by
  classical
  apply (stage F hF xs n).vanish
  by_cases hm : m = n
  · subst m; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply state_monotone F hF xs (Nat.succ_le_of_lt (lt_of_le_of_ne hmn hm))
    change xs m ∈ (state F hF xs (m + 1)).1
    rw [state_succ]
    exact Finset.mem_insert_self _ _

lemma seq_vanish_D {m n : ℕ} (hmn : m < n) {d : X}
    (hd : d ∈ (stage F hF xs m).D) : seq F hF xs n d = 0 := by
  classical
  apply (stage F hF xs n).vanish
  apply Finset.mem_insert_of_mem
  apply state_monotone F hF xs (Nat.succ_le_of_lt hmn)
  change d ∈ (state F hF xs (m + 1)).1
  rw [state_succ]
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hd)

lemma stage_norms_prefix (m : ℕ) (c : ℕ → 𝕜) :
    ∃ d ∈ (stage F hF xs m).D,
      ‖∑ i ∈ Finset.range (m + 1), c i • seq F hF xs i‖ ≤
        2 * ‖(∑ i ∈ Finset.range (m + 1), c i • seq F hF xs i) d‖ := by
  classical
  apply (stage F hF xs m).norming
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hs := state_vectors F hF xs (m + 1)
  rw [state_succ] at hs
  dsimp only at hs
  have : seq F hF xs i ∈ insert (seq F hF xs m) (state F hF xs m).2 := by
    rw [hs]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (Finset.mem_insert.mp this).elim (fun h => Or.inl h) (fun h => Or.inr h)

end NormerStep

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
@[reducible] noncomputable local instance criterionDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance criterionDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

namespace NormerStep
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

/-- The recursive choices satisfy exactly the prefix hypotheses. -/
noncomputable def prefixNormers : PrefixNormers (seq F hF xs) where
  D := fun n => match n with
    | 0 => {0}
    | m + 1 => (stage F hF xs m).D
  unit := by
    intro m d hd
    cases m with
    | zero => have he : d = 0 := Finset.mem_singleton.mp hd
              subst d; simp
    | succ m => exact (stage F hF xs m).unit d hd
  norming := by
    intro m hm c
    cases m with
    | zero => omega
    | succ m => exact stage_norms_prefix F hF xs m c
  vanish := by
    intro m n hmn d hd
    cases m with
    | zero => have he : d = 0 := Finset.mem_singleton.mp hd
              subst d; simp
    | succ m => exact seq_vanish_D F hF xs (Nat.lt_of_succ_le hmn) hd

lemma span_le [IsClosed (F : Set (StrongDual 𝕜 X))] :
    PrefixNormers.closedSpan (seq F hF xs) ≤ F := by
  apply Submodule.topologicalClosure_minimal _ (ht := ‹IsClosed (F : Set (StrongDual 𝕜 X))›)
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact seq_mem F hF xs n

lemma evaluation_x (j : ℕ) :
    PrefixNormers.evaluation (seq F hF xs) (xs j) =
      ∑ i ∈ Finset.range j, seq F hF xs i (xs j) •
        (prefixNormers F hF xs).coord 1 (by norm_num) (fun n => (seq_norm F hF xs n).ge) i := by
  classical
  let H := prefixNormers F hF xs
  have heq : Set.EqOn (NormedSpace.inclusionInDoubleDual 𝕜 X (xs j))
      (∑ i ∈ Finset.range j, seq F hF xs i (xs j) •
        H.ambientCoord 1 (by norm_num) (fun n => (seq_norm F hF xs n).ge) i :
          StrongDual 𝕜 (StrongDual 𝕜 X))
      (closure (Submodule.span 𝕜 (Set.range (seq F hF xs)) : Set (StrongDual 𝕜 X))) := by
    apply ContinuousLinearMap.eqOn_closure_span
    rintro _ ⟨n, rfl⟩
    change seq F hF xs n (xs j) = _
    simp only [sum_apply, smul_apply, H.ambientCoord_basis, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hn : n < j
    · simp [hn]
    · simp [hn, seq_vanish_x F hF xs (Nat.le_of_not_gt hn)]
  ext v
  have hv := heq v.property
  change (v : StrongDual 𝕜 X) (xs j) = _ at hv
  simpa only [PrefixNormers.evaluation_apply, sum_apply, smul_apply, PrefixNormers.coord,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, H] using hv

end NormerStep

/-- The actual evaluation operator on a dual subspace. -/
noncomputable def subspaceEvaluation (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    X →L[𝕜] StrongDual 𝕜 F :=
  (ContinuousLinearMap.precomp 𝕜 F.subtypeL).comp (NormedSpace.inclusionInDoubleDual 𝕜 X)

@[simp] lemma subspaceEvaluation_apply (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (x : X) (f : F) : subspaceEvaluation F x f = (f : StrongDual 𝕜 X) x := rfl

@[reducible] noncomputable local instance criterionSubspaceDualNormedGroup
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedAddCommGroup (StrongDual 𝕜 F) := inferInstance
@[reducible] noncomputable local instance criterionSubspaceDualNormedSpace
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) : NormedSpace 𝕜 (StrongDual 𝕜 F) := inferInstance

/-- A dense sequence of evaluations can be represented by actual vectors of `X`. -/
lemma exists_dense_evaluations (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hsep : TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F))) :
    ∃ xs : ℕ → X, ∀ x : X, subspaceEvaluation F x ∈
      closure (Set.range (fun n => subspaceEvaluation F (xs n))) := by
  classical
  let R := Set.range (subspaceEvaluation F)
  let : TopologicalSpace.SeparableSpace R := hsep.separableSpace
  let : Nonempty R := ⟨⟨subspaceEvaluation F 0, Set.mem_range_self 0⟩⟩
  obtain ⟨ys, hys⟩ := TopologicalSpace.exists_dense_seq R
  choose xs hxs using fun n => (ys n).property
  refine ⟨xs, fun x => ?_⟩
  have he : (fun n => subspaceEvaluation F (xs n)) = fun n => (ys n).val := by
    funext n; exact hxs n
  rw [he]
  have hc := image_closure_subset_closure_image
    (continuous_subtype_val : Continuous (Subtype.val : R → StrongDual 𝕜 F))
    (s := Set.range ys)
  have hm := hc ⟨⟨subspaceEvaluation F x, Set.mem_range_self x⟩,
    hys (⟨subspaceEvaluation F x, Set.mem_range_self x⟩ : R), rfl⟩
  simpa only [← Set.range_comp'] using hm

end SeparableQuotient

end OAI
