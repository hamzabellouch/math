import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Probability.CountingExposurePosterior

namespace OAI

open scoped BigOperators

namespace Balanced.UniformDeletionEnumeration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

def lineEmbedding (f : Direction F → Fin k ↪ F) : (Direction F × Fin k) ↪ Line F where
  toFun t := (t.1, f t.1 t.2)
  inj' := by
    rintro ⟨d, i⟩ ⟨e, j⟩ he
    have hde : d = e := congrArg Prod.fst he
    subst e
    have hij : i = j := (f d).injective (congrArg Prod.snd he)
    subst j
    rfl

def selectedLines (f : Direction F → Fin k ↪ F) : Finset (Line F) :=
  Finset.univ.map (lineEmbedding f)

omit [Field F] [DecidableEq F] in
@[simp] theorem mem_selectedLines (f : Direction F → Fin k ↪ F) (l : Line F) :
    l ∈ selectedLines f ↔ ∃ j, f l.1 j = l.2 := by
  simp only [selectedLines, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨d, j⟩, hj⟩
    have hd : d = l.1 := congrArg Prod.fst hj
    subst d
    exact ⟨j, congrArg Prod.snd hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨(l.1, j), ?_⟩
    change (l.1, f l.1 j) = l
    exact Prod.ext rfl hj

omit [Field F] in

theorem selectedLines_filter (f : Direction F → Fin k ↪ F) (d : Direction F) :
    (selectedLines f).filter (fun l => l.1 = d) =
      Finset.univ.map ((f d).trans
        ⟨Prod.mk d, fun _ _ h => congrArg Prod.snd h⟩) := by
  ext l
  simp only [Finset.mem_filter, mem_selectedLines, Finset.mem_map,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hj⟩, hd⟩
    refine ⟨j, ?_⟩
    change (d, f d j) = l
    apply Prod.ext hd.symm
    simpa only [hd] using hj
  · rintro ⟨j, hj⟩
    change (d, f d j) = l at hj
    have hd : d = l.1 := congrArg Prod.fst hj
    refine ⟨⟨j, ?_⟩, hd.symm⟩
    simpa only [← hd] using congrArg Prod.snd hj

omit [Field F] in

theorem selectedLines_isDeletionSet (f : Direction F → Fin k ↪ F) :
    IsDeletionSet k (selectedLines f) := by
  intro d
  rw [selectedLines_filter]
  simp

def deletionOutcome (f : Direction F → Fin k ↪ F) : DeletionSet F k :=
  ⟨selectedLines f, selectedLines_isDeletionSet f⟩

theorem deletionOutcome_surjective :
    Function.Surjective (deletionOutcome (F := F) (k := k)) := by
  intro D
  let S (d : Direction F) := D.val.filter (fun l => l.1 = d)
  have hcard (d : Direction F) : Fintype.card (S d) = k := by
    rw [Fintype.card_coe]
    exact D.property d
  let e (d : Direction F) : Fin k ≃ S d := (Fintype.equivFinOfCardEq (hcard d)).symm
  let f (d : Direction F) : Fin k ↪ F :=
    ⟨fun j => (e d j).val.2, by
      intro i j hij
      apply (e d).injective
      apply Subtype.ext
      apply Prod.ext
      · exact ((Finset.mem_filter.mp (e d i).property).2).trans
          ((Finset.mem_filter.mp (e d j).property).2).symm
      · exact hij⟩
  refine ⟨f, Subtype.ext ?_⟩
  ext l
  change l ∈ selectedLines f ↔ l ∈ D.val
  rw [mem_selectedLines]
  constructor
  · rintro ⟨j, hj⟩
    have hmem := (Finset.mem_filter.mp (e l.1 j).property).1
    have heq : (e l.1 j).val = l := by
      apply Prod.ext
      · exact (Finset.mem_filter.mp (e l.1 j).property).2
      · exact hj
    exact heq ▸ hmem
  · intro hl
    let x : S l.1 := ⟨l, Finset.mem_filter.mpr ⟨hl, rfl⟩⟩
    refine ⟨(e l.1).symm x, ?_⟩
    change ((e l.1) ((e l.1).symm x)).val.2 = l.2
    simp [x]

def lineRelabel (τ : Direction F → Equiv.Perm F) : Line F ≃ Line F where
  toFun l := (l.1, τ l.1 l.2)
  invFun l := (l.1, (τ l.1).symm l.2)
  left_inv l := by cases l; simp
  right_inv l := by cases l; simp

def arrayRelabel (τ : Direction F → Equiv.Perm F) :
    (Direction F → Fin k ↪ F) ≃ (Direction F → Fin k ↪ F) :=
  Equiv.piCongrRight fun d => InjectionExposureLaw.postcompose (τ d)

omit [Field F] [DecidableEq F] in

theorem selectedLines_relabel (τ : Direction F → Equiv.Perm F)
    (f : Direction F → Fin k ↪ F) :
    selectedLines (arrayRelabel τ f) = (selectedLines f).map (lineRelabel τ).toEmbedding := by
  unfold selectedLines
  rw [Finset.map_map]
  congr 1

theorem exists_relabel_outcomes (D E : DeletionSet F k) :
    ∃ τ : Direction F → Equiv.Perm F,
      D.val.map (lineRelabel τ).toEmbedding = E.val := by
  obtain ⟨f, rfl⟩ := deletionOutcome_surjective D
  obtain ⟨g, rfl⟩ := deletionOutcome_surjective E
  have hex (d : Direction F) := Equiv.Perm.exists_extending_pair
    (f d) (g d) (f d).injective (g d).injective
  choose τ hτ using hex
  refine ⟨τ, ?_⟩
  change (selectedLines f).map (lineRelabel τ).toEmbedding = selectedLines g
  rw [← selectedLines_relabel]
  congr 1
  funext d
  apply Function.Embedding.ext
  intro j
  exact hτ d j

theorem outcome_fiber_card_eq (D E : DeletionSet F k) :
    ((Finset.univ.filter (fun f : Direction F → Fin k ↪ F => deletionOutcome f = D)).card) =
      ((Finset.univ.filter (fun f : Direction F → Fin k ↪ F => deletionOutcome f = E)).card) := by
  obtain ⟨τ, hτ⟩ := exists_relabel_outcomes D E
  apply Finset.card_equiv (arrayRelabel τ)
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    apply Subtype.ext
    change selectedLines (arrayRelabel τ f) = E.val
    rw [selectedLines_relabel]
    have hv : selectedLines f = D.val := congrArg Subtype.val hf
    rw [hv, hτ]
  · intro hf
    apply Subtype.ext
    change selectedLines f = D.val
    apply Finset.map_injective (lineRelabel τ).toEmbedding
    rw [hτ, ← selectedLines_relabel]
    exact congrArg Subtype.val hf

theorem expect_deletionOutcome (h : Direction F → Fin k ↪ F)
    (g : DeletionSet F k → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F, g (deletionOutcome f)) =
      𝔼 D : DeletionSet F k, g D := by
  let m := ((Finset.univ : Finset (Direction F → Fin k ↪ F)).filter
    (fun f => deletionOutcome f = deletionOutcome h)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨h, by simp⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq Finset.univ Finset.univ
    deletionOutcome m hm (fun _ _ => Finset.mem_univ _)
  intro D _
  exact outcome_fiber_card_eq D (deletionOutcome h)

theorem deletionOutcome_probability (h : Direction F → Fin k ↪ F)
    (D : DeletionSet F k) :
    (𝔼 f : Direction F → Fin k ↪ F,
      if deletionOutcome f = D then (1 : ℝ) else 0) = uniformDeletionMass (F := F) k := by
  rw [expect_deletionOutcome h (fun E => if E = D then (1 : ℝ) else 0)]
  simp [uniformDeletionMass]

def tokenEquiv (f : Direction F → Fin k ↪ F) :
    (Direction F × Fin k) ≃ (deletionOutcome f).val :=
  Equiv.ofBijective
    (fun t => (⟨lineEmbedding f t, Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩ :
      (deletionOutcome f).val))
    ⟨fun _ _ he => (lineEmbedding f).injective (congrArg Subtype.val he), by
      intro l
      obtain ⟨t, _, ht⟩ := Finset.mem_map.mp l.property
      exact ⟨t, Subtype.ext ht⟩⟩

def orderingEquiv (f : Direction F → Fin k ↪ F) :
    Equiv.Perm (Direction F × Fin k) ≃
      ((Direction F × Fin k) ≃ (deletionOutcome f).val) where
  toFun π := π.trans (tokenEquiv f)
  invFun e := e.trans (tokenEquiv f).symm
  left_inv π := by
    apply Equiv.ext
    intro t
    exact (tokenEquiv f).symm_apply_apply (π t)
  right_inv e := by
    apply Equiv.ext
    intro t
    exact (tokenEquiv f).apply_symm_apply (e t)

theorem expect_ordering (f : Direction F → Fin k ↪ F)
    (g : ((Direction F × Fin k) ≃ (deletionOutcome f).val) → ℝ) :
    (𝔼 π : Equiv.Perm (Direction F × Fin k), g (π.trans (tokenEquiv f))) =
      𝔼 e : (Direction F × Fin k) ≃ (deletionOutcome f).val, g e := by
  apply Fintype.expect_equiv (orderingEquiv f)
  intro π
  rfl

theorem expect_uniform_deletion_and_order (h : Direction F → Fin k ↪ F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F,
      𝔼 π : Equiv.Perm (Direction F × Fin k),
        g (deletionOutcome f) (π.trans (tokenEquiv f))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e := by
  calc
    _ = 𝔼 f : Direction F → Fin k ↪ F,
        𝔼 e : (Direction F × Fin k) ≃ (deletionOutcome f).val,
          g (deletionOutcome f) e := by
      apply Finset.expect_congr rfl
      intro f _
      exact expect_ordering f (g (deletionOutcome f))
    _ = _ := expect_deletionOutcome h
      (fun D => 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e)

def canonicalOffsets (hk : k ≤ Fintype.card F) : Direction F → Fin k ↪ F :=
  fun _ => (Fin.castLEEmb hk).trans (Fintype.equivFin F).symm.toEmbedding

theorem expect_uniform_deletion_and_order_of_le (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F,
      𝔼 π : Equiv.Perm (Direction F × Fin k),
        g (deletionOutcome f) (π.trans (tokenEquiv f))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e :=
  expect_uniform_deletion_and_order (canonicalOffsets hk) g

theorem expect_originalExperiment (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 ω : CountingExposurePosterior.Experiment
        (G := Direction F) (ι := Fin k) (α := F),
      g (deletionOutcome ω.2) (ω.1.trans (tokenEquiv ω.2))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e := by
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  exact expect_uniform_deletion_and_order_of_le hk g

theorem orderedLine_eq_nextLine
    (ω : CountingExposurePosterior.Experiment
      (G := Direction F) (ι := Fin k) (α := F)) (i : Direction F × Fin k) :
    ((ω.1.trans (tokenEquiv ω.2)) i).val =
      CountingExposurePosterior.nextLine ω i := rfl

omit [Field F] [DecidableEq F] in

theorem card_tokens : Fintype.card (Direction F × Fin k) = k * (Fintype.card F + 1) := by
  simp [Direction, Nat.mul_comm]

def timeToToken : Fin (k * (Fintype.card F + 1)) ≃ (Direction F × Fin k) :=
  (Fintype.equivFinOfCardEq card_tokens).symm

def timeOrderingEquiv (D : DeletionSet F k) :
    ((Direction F × Fin k) ≃ D.val) ≃ (Fin (k * (Fintype.card F + 1)) ≃ D.val) where
  toFun e := timeToToken.trans e
  invFun e := timeToToken.symm.trans e
  left_inv e := by
    apply Equiv.ext
    intro t
    exact congrArg e (timeToToken.apply_symm_apply t)
  right_inv e := by
    apply Equiv.ext
    intro t
    exact congrArg e (timeToToken.symm_apply_apply t)

theorem expect_originalExperiment_time (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → (Fin (k * (Fintype.card F + 1)) ≃ D.val) → ℝ) :
    (𝔼 ω : CountingExposurePosterior.Experiment
        (G := Direction F) (ι := Fin k) (α := F),
      g (deletionOutcome ω.2) (timeToToken.trans (ω.1.trans (tokenEquiv ω.2)))) =
      𝔼 D : DeletionSet F k,
        𝔼 e : Fin (k * (Fintype.card F + 1)) ≃ D.val, g D e := by
  rw [expect_originalExperiment hk (fun D e => g D (timeToToken.trans e))]
  apply Finset.expect_congr rfl
  intro D _
  apply Fintype.expect_equiv (timeOrderingEquiv D)
  intro e
  rfl

end
end Balanced.UniformDeletionEnumeration

end OAI
