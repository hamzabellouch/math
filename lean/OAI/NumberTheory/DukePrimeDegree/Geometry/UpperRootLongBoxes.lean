import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDisintegration
import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnipotentFreeness

namespace OAI

/-!
# Long boxes for the full positive-root group

The ordered root word is injective. Generic arithmetic lattices have
free upper unipotent orbits, so every compact set of full root times
fits into one actual quotient box containing the chosen basepoint.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma allPositiveRoots_closed (n : ℕ) :
    ∀ a b c : Fin n, (a, b) ∈ allPositiveRoots n → (b, c) ∈ allPositiveRoots n →
      (a, c) ∈ allPositiveRoots n := by
  intro a b c hab hbc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_trans (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hbc).2⟩

theorem ae_upperRoot_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ g ∈ positiveRootGeneratedGroup (allPositiveRoots (d + 1)),
      rightAction x g = x → g = 1 := by
  filter_upwards [ae_positiveRootPattern_stabilizer_trivial d μ hA] with x hx g hg hfix
  exact hx (allPositiveRoots (d + 1)) (fun p hp => (Finset.mem_filter.mp hp).2) g
    (positiveRootGeneratedGroup_pattern _ (allPositiveRoots_closed _) hg) hfix

theorem upperRootWord_injective (n : ℕ) : Function.Injective (completeRootChain n).word := by
  intro t u h
  have he : upperRootParam n (upperRootIdentity n, t) =
      upperRootParam n (upperRootIdentity n, u) := by
    rw [upperRootParam_eq_mul, upperRootParam_eq_mul, h]
  exact congrArg Prod.snd ((upperRootParam_isOpenEmbedding n).injective he)

lemma upperRootQuotientParam_zero (n : ℕ) (g : G n) (s : UpperRootTransverse n) :
    upperRootQuotientParam n g (s, (completeRootChain n).zeroTime) = Quotient.mk _ (g * s.val) := by
  unfold upperRootQuotientParam
  rw [upperRootParam_eq_mul, EliminationChain.word_zeroTime, mul_one]

theorem upperRootQuotientParam_injective_of_free (n : ℕ) (g : G n)
    (s : UpperRootTransverse n)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (Quotient.mk _ (g * s.val)) v = Quotient.mk _ (g * s.val) → v = 1) :
    Function.Injective (fun t => upperRootQuotientParam n g (s, t)) := by
  intro t u h
  let wt := (completeRootChain n).word t
  let wu := (completeRootChain n).word u
  have hm : wt * wu⁻¹ ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    (positiveRootGeneratedGroup _).mul_mem (upperRootWord_mem n t)
      ((positiveRootGeneratedGroup _).inv_mem (upperRootWord_mem n u))
  have hh := congrArg (fun x => rightAction x wu⁻¹) h
  change rightAction (upperRootQuotientParam n g (s, t)) wu⁻¹ =
    rightAction (upperRootQuotientParam n g (s, u)) wu⁻¹ at hh
  rw [upperRootQuotientParam_eq_action, upperRootQuotientParam_eq_action,
    rightAction_mul, rightAction_mul] at hh
  have hz : rightAction (Quotient.mk _ (g * s.val)) (wt * wu⁻¹) =
      Quotient.mk _ (g * s.val) := by
    simpa only [wt, wu, mul_inv_cancel, rightAction_one] using hh
  have he := hfree (wt * wu⁻¹) hm hz
  apply upperRootWord_injective n
  exact mul_right_cancel (show wt * wu⁻¹ = wu * wu⁻¹ from he.trans (mul_inv_cancel wu).symm)

theorem upperRootBox_contains_compact_time (n : ℕ) (g : G n)
    (s : UpperRootTransverse n)
    (hinj : Function.Injective (fun t => upperRootQuotientParam n g (s, t)))
    (K : Set (UpperRootTime n)) (hK : IsCompact K) :
    ∃ B : UpperRootBox n g, s ∈ B.transverse ∧ K ⊆ B.time := by
  have hf := upperRootQuotientParam_localHomeomorph n g
  have hi : Set.InjOn (upperRootQuotientParam n g) ({s} ×ˢ K) := by
    rintro ⟨s₁, t₁⟩ ⟨hs₁, _⟩ ⟨s₂, t₂⟩ ⟨hs₂, _⟩ heq
    have h₁ : s₁ = s := hs₁
    have h₂ : s₂ = s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W, hW, hKW, hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod hK) hi
  obtain ⟨U, V, hU, hV, hsU, hTV, hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (UpperRootTransverse n))) hK hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U, V, hU, hV, he⟩, hsU (Set.mem_singleton s), hTV⟩

theorem upperRootBox_arbitrary_compact_of_free (n : ℕ) (x : X n)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (K : Set (UpperRootTime n)) (hK : IsCompact K) :
    ∃ (g : G n) (B : UpperRootBox n g), upperRootIdentity n ∈ B.transverse ∧
      (completeRootChain n).zeroTime ∈ B.time ∧ K ⊆ B.time ∧
        upperRootQuotientParam n g (upperRootIdentity n, (completeRootChain n).zeroTime) = x := by
  induction x using Quotient.inductionOn with
  | h g =>
    have hf : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
        rightAction (Quotient.mk _ (g * (upperRootIdentity n).val)) v =
          Quotient.mk _ (g * (upperRootIdentity n).val) → v = 1 := by
      simpa only [upperRootIdentity, mul_one] using hfree
    have hi := upperRootQuotientParam_injective_of_free n g (upperRootIdentity n) hf
    obtain ⟨B, hs, hKB⟩ := upperRootBox_contains_compact_time n g (upperRootIdentity n) hi
      (K ∪ {(completeRootChain n).zeroTime}) (hK.union isCompact_singleton)
    refine ⟨g, B, hs, hKB (Or.inr rfl), fun _ h => hKB (Or.inl h), ?_⟩
    rw [upperRootQuotientParam_zero]
    simp only [upperRootIdentity, mul_one]

end DukePrimeDegree

end

end OAI
