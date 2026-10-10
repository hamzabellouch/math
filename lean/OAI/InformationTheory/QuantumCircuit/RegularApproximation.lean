import OAI.InformationTheory.QuantumCircuit.SpectralIdentities

namespace OAI

/-! Polynomial approximations on regular quantum trajectories. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Filter

namespace QAC

def Count.Subcount {N : ℕ} (A M : Count N) : Prop :=
  A.support ⊆ M.support ∧ ∀ i ∈ A.support, A.vector i = M.vector i

lemma Count.Subcount.refl {N : ℕ} (M : Count N) : M.Subcount M := ⟨Finset.Subset.refl _, by simp⟩

lemma Count.Subcount.trans {N : ℕ} {A B M : Count N}
    (h : A.Subcount B) (h' : B.Subcount M) : A.Subcount M :=
  ⟨h.1.trans h'.1, fun i hi => (h.2 i hi).trans (h'.2 i (h.1 hi))⟩

lemma Count.Subcount.zero_eq {N : ℕ} {A M : Count N} (h : A.Subcount M) :
    A.zero = (M.restrict A.support).zero := by
  classical
  dsimp only [Count.zero, Count.restrict]
  congr 1
  funext i
  by_cases hi : i ∈ A.support
  · simp [hi, h.1 hi, h.2 i hi]
  · simp [hi]

lemma Count.subcount_join_left {N : ℕ} (A B : Count N) : A.Subcount (A.join B) := by
  classical
  exact ⟨Finset.subset_union_left, by intro i hi; simp [Count.join, hi]⟩

lemma Count.subcount_join_right {N : ℕ} (A B : Count N)
    (h : Disjoint A.support B.support) : B.Subcount (A.join B) := by
  classical
  refine ⟨Finset.subset_union_right, ?_⟩
  intro i hi
  have hn : i ∉ A.support := fun ha => Finset.disjoint_left.mp h ha hi
  simp [Count.join, hn]

lemma Count.Subcount.join {N : ℕ} {A B M : Count N}
    (hA : A.Subcount M) (hB : B.Subcount M) : (A.join B).Subcount M := by
  classical
  refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
  intro i hi
  change (if i ∈ A.support then A.vector i else B.vector i) = M.vector i
  split_ifs with ha
  · exact hA.2 i ha
  · exact hB.2 i ((Finset.mem_union.mp hi).resolve_left ha)

lemma jointTest_support {N : ℕ} (l : List (Count N)) (i : Fin N) :
    i ∈ (jointTest l).support ↔ ∃ A ∈ l, i ∈ A.support := by
  induction l with
  | nil => simp [jointTest, Count.empty]
  | cons A l ih => simp [jointTest, Count.join, ih, or_and_right, exists_or]

lemma jointTest_disjoint {N : ℕ} (A : Count N) (l : List (Count N))
    (h : ∀ B ∈ l, Disjoint A.support B.support) :
    Disjoint A.support (jointTest l).support := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨B, hB, hiB⟩ := (jointTest_support l i).mp hj
  exact Finset.disjoint_left.mp (h B hB) hi hiB

lemma jointTest_subcount {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ∀ A ∈ l, A.Subcount (jointTest l) := by
  induction l with
  | nil => simp
  | cons A l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact Count.subcount_join_left _ _
    · exact (ih hl B hB).trans (Count.subcount_join_right _ _ (jointTest_disjoint A l ha))

lemma reflectionTerms_subcount {N : ℕ} (l : List (Count N)) (M : Count N)
    (hl : ∀ A ∈ l, A.Subcount M) : ∀ p ∈ reflectionTerms l, p.2.Subcount M := by
  induction l with
  | nil => simp [reflectionTerms, Count.Subcount, Count.empty]
  | cons A l ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih (fun B hb => hl B (List.mem_cons_of_mem _ hb)) p hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hl A (List.mem_cons_self ..)).join
        (ih (fun B hb => hl B (List.mem_cons_of_mem _ hb)) q hq)

lemma TensorSupported.disjoint_commute {N : ℕ} {J K : Finset (Fin N)}
    {A B : Operator N} (hA : TensorSupported J A) (hB : TensorSupported K B)
    (h : Disjoint J K) : Commute A B := by
  classical
  rcases hA with ⟨a, rfl, ha⟩
  rcases hB with ⟨b, rfl, hb⟩
  show tensorMatrix a * tensorMatrix b = tensorMatrix b * tensorMatrix a
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · have hik : i ∉ K := Finset.disjoint_left.mp h hi
    simp [hb i hik]
  · simp [ha i hi]

lemma Count.zero_supported {N : ℕ} (A : Count N) : TensorSupported A.support A.zero :=
  ⟨_, rfl, by intro i hi; simp [hi]⟩

lemma localMatrix_supported {N : ℕ} (L : LocalLayer N) (J : Finset (Fin N))
    (h : ∀ i ∉ J, L i = 1) : TensorSupported J (localMatrix L) :=
  ⟨_, rfl, by intro i hi; simp [h i hi]⟩

def ReflectionLayer.touching {N : ℕ} (R : ReflectionLayer N) (J : Finset (Fin N)) :
    ReflectionLayer N where
  gates := R.gates.filter (fun D => decide (¬Disjoint D.support J))
  disjoint := R.disjoint.filter _

lemma ReflectionLayer.touching_length {N : ℕ} (R : ReflectionLayer N)
    (J : Finset (Fin N)) : (R.touching J).gates.length ≤ J.card := by
  apply list_disjoint_hits_length Count.support _ (R.touching J).disjoint
  intro D hD
  have h := (List.mem_filter.mp hD).2
  simp only [decide_eq_true_eq] at h
  exact Finset.not_disjoint_iff_nonempty_inter.mp h

lemma ReflectionLayer.touching_conjugate {N : ℕ} (R : ReflectionLayer N)
    (J : Finset (Fin N)) (D : Operator N) (hD : TensorSupported J D) :
    conjugate (reflectionMatrix R) D = conjugate (reflectionMatrix (R.touching J)) D := by
  rw [reflectionMatrix_eq, reflectionMatrix_eq]
  apply list_conjugate_filter
  · exact R.disjoint.imp (fun h => reflect_disjoint_commute _ _ h)
  · intro A _; exact reflect_unitary A
  · intro A _ hA
    have hd : Disjoint A.support J := by simpa using hA
    exact (Commute.one_left _).sub_left ((A.zero_supported.disjoint_commute hD hd).smul_left (2 : ℝ))

def interiorTerm {N : ℕ} (M : Count N) (J S T : Finset (Fin N))
    (D : Operator N) : Operator N :=
  (M.restrict (S ∩ J)).zero * D * (M.restrict (T ∩ J)).zero

lemma interiorTerm_supported {N : ℕ} (M : Count N) (J S T : Finset (Fin N))
    (D : Operator N) (hD : TensorSupported J D) :
    TensorSupported J (interiorTerm M J S T D) := by
  rcases hD with ⟨a, rfl, ha⟩
  refine ⟨fun i =>
    (if i ∈ (M.restrict (S ∩ J)).support then rankOne (M.vector i) else 1) * a i *
    (if i ∈ (M.restrict (T ∩ J)).support then rankOne (M.vector i) else 1), ?_, ?_⟩
  · unfold interiorTerm Count.zero
    rw [tensorMatrix_mul, tensorMatrix_mul]
    rfl
  · intro i hi
    simp [Count.restrict, hi, ha i hi]

lemma interiorTerm_norm {N : ℕ} (M : Count N) (J S T : Finset (Fin N))
    (D : Operator N) (hD : ‖D‖ ≤ 1) : ‖interiorTerm M J S T D‖ ≤ 1 :=
  norm_mul_le_one
    (norm_mul_le_one (IsStarProjection.norm_le _ (M.restrict _).zero_projection) hD)
    (IsStarProjection.norm_le _ (M.restrict _).zero_projection)

lemma sandwich_factor {N : ℕ} (M : Count N) (J S T : Finset (Fin N))
    (D : Operator N) (hD : TensorSupported J D) :
    (M.restrict S).zero * D * (M.restrict T).zero =
      interiorTerm M J S T D * (M.restrict ((S ∪ T) \ J)).zero := by
  classical
  rcases hD with ⟨a, rfl, ha⟩
  unfold interiorTerm Count.zero
  simp only [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hm : i ∈ M.support
  · have hid := (rankOne_projection (M.normalized i hm)).isIdempotentElem.eq
    by_cases hj : i ∈ J
    · by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp [Count.restrict, hm, hj, hs, ht]
    · by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp [Count.restrict, hm, hj, hs, ht, ha i hj, hid]
  · simp [Count.restrict, hm]

lemma Count.restrict_zero_pattern_commute {N : ℕ} (M : Count N)
    (J F : Finset (Fin N)) : Commute (M.restrict J).zero (M.pattern F) := by
  classical
  change (M.restrict J).zero * M.pattern F = M.pattern F * (M.restrict J).zero
  unfold Count.zero Count.pattern
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hm : i ∈ M.support
  · by_cases hj : i ∈ J <;> by_cases hf : i ∈ F <;>
      simp [Count.restrict, hm, hj, hf, mul_sub, sub_mul]
  · simp [Count.restrict, hm]

lemma Count.restrict_zero_high_commute {N : ℕ} (M : Count N)
    (J : Finset (Fin N)) (r : ℝ) : Commute (M.restrict J).zero (M.high r) := by
  classical
  change (M.restrict J).zero * M.high r = M.high r * (M.restrict J).zero
  rw [Count.high, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs
  · exact (M.restrict_zero_pattern_commute J F).eq
  · simp

lemma Count.restrict_high_absorb (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (M : Count N) (J : Finset (Fin N)) (r : ℝ) :
    (M.restrict J).high r * M.high r = (M.restrict J).high r := by
  classical
  have hleft : M.high r * (M.restrict J).high r = (M.restrict J).high r := by
    rw [hspec.restriction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro F hF
    by_cases hr : r ≤ ((F ∩ J).card : ℝ)
    · simp only [hr, ite_true]
      rw [M.high_mul_pattern F (Finset.mem_powerset.mp hF)]
      exact ite_eq_left (hr.trans (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left))
    · simp [hr]
  have := congrArg star hleft
  simpa only [star_mul, (M.high_projection r).isSelfAdjoint.star_eq,
    ((M.restrict J).high_projection r).isSelfAdjoint.star_eq] using this

lemma Count.restrict_high_action_le (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (M : Count N) (J : Finset (Fin N)) (r : ℝ) (ψ : State N) :
    ‖act ((M.restrict J).high r) ψ‖ ≤ ‖act (M.high r) ψ‖ := by
  rw [← M.restrict_high_absorb hspec J r, act_mul]
  exact act_norm_le_of_contraction _ (IsStarProjection.norm_le _ ((M.restrict J).high_projection r)) _

lemma Count.polynomial_action_error {N : ℕ} (M : Count N) (p : Polynomial ℝ)
    (ψ : State N) (r δ τ : ℝ) (hδ : 0 ≤ δ) (hψ : ‖ψ‖ ≤ 1)
    (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ‖act (M.high r) ψ‖ ≤ τ) :
    ‖act (M.zero - M.polynomial p) ψ‖ ≤ δ + (1 + weight N p) * τ := by
  have hsplit : M.zero - M.polynomial p =
      (M.zero - M.polynomial p) * M.low r + (M.zero - M.polynomial p) * M.high r := by
    dsimp [Count.low]; noncomm_ring
  rw [hsplit, act_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (act_norm_le _ _).trans ((mul_le_mul_of_nonneg_right
      (M.polynomial_error_low p hδ hp0 hp) (norm_nonneg _)).trans
      (by simpa using mul_le_mul_of_nonneg_left hψ hδ))
  · rw [act_mul]
    have hw : 0 ≤ 1 + weight N p := by have := weight_nonneg (Nat.cast_nonneg N) p; linarith
    exact (act_norm_le _ _).trans (mul_le_mul
      ((norm_sub_le _ _).trans (add_le_add
        (IsStarProjection.norm_le _ M.zero_projection) (M.polynomial_norm_le p)))
      htail (norm_nonneg _) hw)

end QAC

end

end OAI
