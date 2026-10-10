import OAI.Combinatorics.ParityLifts.PureComponents

namespace OAI

namespace ParityWL

open scoped BigOperators

section PureTotals

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def pureLeftTotalEquiv :
    ((x : Fin k → V) × F.Maps (G.sum H) (Sum.inl ∘ x)) ≃ PureLeftMaps F G H where
  toFun f := ⟨f.2.1, fun i => by rw [f.2.2 i]; rfl⟩
  invFun f := ⟨fun i => (f.1.1 (F.roots i)).getLeft (f.2 i),
    ⟨f.1, fun i => (Sum.inl_getLeft _ _).symm⟩⟩
  left_inv f := by
    rcases f with ⟨x, f, hf⟩
    have hx : (fun i => (f.1 (F.roots i)).getLeft (by rw [hf i]; rfl)) = x := by
      funext i
      exact (Sum.getLeft_eq_iff _).mpr (hf i)
    dsimp only
    apply Sigma.ext hx
    apply (Subtype.heq_iff_coe_eq (fun g => by dsimp only; rw [hx])).mpr
    rfl
  right_inv _ := rfl

lemma sum_pureLeft_count [Fintype V] [Fintype W] :
    ∑ x : Fin k → V, F.count (G.sum H) (Sum.inl ∘ x) =
      (Fintype.card (PureLeftMaps F G H) : ℚ) := by
  unfold RootedTest.count
  rw [← Nat.cast_sum, ← Fintype.card_sigma, Fintype.card_congr (pureLeftTotalEquiv F G H)]

noncomputable def rootedMapsIso {U : Type} {K : SimpleGraph U} (e : G ≃g K) (x : Fin k → V) :
    F.Maps G x ≃ F.Maps K (e ∘ x) where
  toFun f := ⟨⟨e ∘ f.1.1, fun a b hab => e.map_adj_iff.mpr (f.1.2 a b hab)⟩,
    fun i => congrArg e (f.2 i)⟩
  invFun f := ⟨⟨e.symm ∘ f.1.1, fun a b hab => e.symm.map_adj_iff.mpr (f.1.2 a b hab)⟩,
    fun i => by simpa only [Function.comp_apply, e.symm_apply_apply] using congrArg e.symm (f.2 i)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact e.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact e.apply_symm_apply _

lemma count_pureRight_swap [Fintype V] [Fintype W] (x : Fin k → W) :
    F.count (G.sum H) (Sum.inr ∘ x) = F.count (H.sum G) (Sum.inl ∘ x) := by
  have he := Fintype.card_congr (rootedMapsIso F (G.sum H)
    (SimpleGraph.Iso.sumComm : G.sum H ≃g H.sum G) (Sum.inr ∘ x))
  exact congrArg (fun n : ℕ => (n : ℚ)) he

lemma sum_pureRight_count [Fintype V] [Fintype W] :
    ∑ x : Fin k → W, F.count (G.sum H) (Sum.inr ∘ x) =
      (Fintype.card (PureLeftMaps F H G) : ℚ) := by
  simp only [count_pureRight_swap, sum_pureLeft_count]

lemma no_choice_equal_pure_total (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful) :
    ∑ x, F.count ((zeroLift C).sum (starLift C)) (Sum.inl ∘ x) =
      ∑ x, F.count ((zeroLift C).sum (starLift C)) (Sum.inr ∘ x) := by
  rw [sum_pureLeft_count, sum_pureRight_count, pureLeft_card, pureLeft_card]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply Finset.sum_congr rfl
  intro s _
  have hl := no_choice_equal_relation C ht hn
    (fun a b : MaskLeft F s => F.relation a.1 b.1)
    ⟨fun a b h => F.symmetric.symm a.1 b.1 h⟩ (F.tree.induce (fun a => s.1 a = true))
  have hr := no_choice_equal_relation C ht hn
    (fun a b : MaskRight F s => F.relation a.1 b.1)
    ⟨fun a b h => F.symmetric.symm a.1 b.1 h⟩ (F.tree.induce (fun a => s.1 a = false))
  rw [hl, hr]

end PureTotals

theorem no_choice_pure_equivalent (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hn : ¬ C.Successful) :
    PureWLEquivalent (zeroLift C) (starLift C) c k := by
  classical
  intro r
  let U := (zeroLift C).sum (starLift C)
  cases c with
  | joint =>
    exact histograms_eq_of_tests U U
      (fun x => Sum.inl (Sum.inl ∘ x)) (fun x => Sum.inr (Sum.inr ∘ x))
      (pairJoint U U k r) (joint_indicator_mem _ _ (t := k+1) le_rfl r)
      (fun F => no_choice_equal_pure_total F C (by omega) hn)
  | separate =>
    exact histograms_eq_of_tests U U
      (fun x => Sum.inl (Sum.inl ∘ x)) (fun x => Sum.inr (Sum.inr ∘ x))
      (pairSeparate U U k r) (separate_indicator_mem _ _ (t := k) le_rfl r)
      (fun F => no_choice_equal_pure_total F C (by omega) hn)

/-- The parity reduction on the explicitly constructed
uncolored simple lifts, including empty choice domains. -/
theorem parity_reduction : ParityReductionStatement := by
  intro k hk c C
  have ht : 2 ≤ bagParameter c k := by cases c <;> simp only [bagParameter] <;> omega
  refine ⟨choice_lifts_equal_order ht C, ?_, ?_, ?_, successful_detected k hk c C⟩
  · intro A _ hA
    exact choice_lift_order_bound ht C A hA (fun _ => 0)
  · exact ⟨equivalent_no_choice k hk c C, no_choice_equivalent k hk c C⟩
  · exact ⟨pure_equivalent_no_choice k hk c C, no_choice_pure_equivalent k hk c C⟩

end ParityWL

end OAI
