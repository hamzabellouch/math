import OAI.Combinatorics.DiscreteConvexity.CoveringBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-!
# Deterministic covers from a pair-sampling outcome

Every sampling outcome gives a cover.  The cost bounds count generators
with multiplicity, indexed by ordered pairs or injective ordered tuples.
No independence or probability estimate is needed for these pointwise
statements.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The generator produced by a sampled ordered pair. -/
def pairUnion {H : Family V} (p : PairIndex H) : Finset V := p.1.val ∪ p.2.val

/-- Duplicate unions are identified in the family of sampled generators. -/
noncomputable def sampledFamily (H : Family V) (sample : Sample H) : Family V :=
  sample.image pairUnion

/-- An injective tuple contributes a residual generator exactly when all
of its ordered pair indices were avoided. -/
noncomputable def residualFamily (H : Family V) (m : ℕ) (sample : Sample H) :
    Family V := by
  classical
  exact (Finset.univ.filter
    (fun f : EdgeTuple H m => Disjoint sample (tuplePairs f))).image tupleUnion

@[simp] theorem mem_sampledFamily {H : Family V} {sample : Sample H} {I : Finset V} :
    I ∈ sampledFamily H sample ↔ ∃ p ∈ sample, pairUnion p = I := by
  classical
  simp [sampledFamily]

@[simp] theorem mem_residualFamily {H : Family V} {m : ℕ}
    {sample : Sample H} {I : Finset V} :
    I ∈ residualFamily H m sample ↔
      ∃ f : EdgeTuple H m, Disjoint sample (tuplePairs f) ∧ tupleUnion f = I := by
  classical
  simp [residualFamily]

/-- Counting each sampled ordered pair separately bounds the family cost. -/
theorem cost_sampledFamily_le (H : Family V) (sample : Sample H)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    cost rho (sampledFamily H sample) ≤
      ∑ p ∈ sample, rho ^ (pairUnion p).card := by
  classical
  unfold cost sampledFamily
  exact Finset.sum_image_le_of_nonneg
    (fun I _ => pow_nonneg hrho I.card)

/-- Counting each avoiding tuple separately bounds the residual cost.
The indicator has the same argument order as the sampling law. -/
theorem cost_residualFamily_le (H : Family V) (m : ℕ) (sample : Sample H)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    cost rho (residualFamily H m sample) ≤
      ∑ f : EdgeTuple H m,
        if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0 := by
  classical
  calc
    cost rho (residualFamily H m sample) ≤
        ∑ f ∈ Finset.univ.filter
            (fun f : EdgeTuple H m => Disjoint sample (tuplePairs f)),
          rho ^ (tupleUnion f).card := by
      unfold cost residualFamily
      exact Finset.sum_image_le_of_nonneg
        (fun I _ => pow_nonneg hrho I.card)
    _ = _ := Finset.sum_filter _ _

/-- A large contained-edge family can be enumerated injectively inside
the regular edges, provided the set avoids the initial generators. -/
theorem exists_regular_tuple {H C0 : Family V} {m : ℕ} {S : Finset V}
    (hm : m ≤ (H.filter (fun e => e ⊆ S)).card)
    (h0 : ¬∃ I ∈ C0, I ⊆ S) :
    ∃ f : EdgeTuple (regularFamily H C0) m, ∀ i, (f.val i).val ⊆ S := by
  classical
  let K := H.filter (fun e => e ⊆ S)
  have hKregular : K ⊆ regularFamily H C0 := by
    intro e he
    obtain ⟨heH, heS⟩ := Finset.mem_filter.mp he
    refine mem_regularFamily.mpr ⟨heH, ?_⟩
    intro I hI hIe
    exact h0 ⟨I, hI, Finset.Subset.trans hIe heS⟩
  have hcard : Fintype.card (Fin m) ≤ Fintype.card ↥K := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hm
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let f : EdgeTuple (regularFamily H C0) m :=
    ⟨fun i => ⟨(g i).val, hKregular (g i).property⟩, by
      intro i j hij
      apply g.injective
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥(regularFamily H C0) → Finset V) hij⟩
  refine ⟨f, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (g i).property).2

/-- Every pair-sampling outcome covers each set containing sufficiently
many original edges.  This includes `m = 0` and empty edge families. -/
theorem covers_sampled_residual [Fintype V] (H C0 : Family V) (m : ℕ)
    (sample : Sample (regularFamily H C0)) :
    Covers (C0 ∪ sampledFamily (regularFamily H C0) sample ∪
      residualFamily (regularFamily H C0) m sample) (denseFamily H m) := by
  classical
  intro S hS
  by_cases h0 : ∃ I ∈ C0, I ⊆ S
  · obtain ⟨I, hI, hIS⟩ := h0
    exact ⟨I, Finset.mem_union_left _ (Finset.mem_union_left _ hI), hIS⟩
  · obtain ⟨f, hf⟩ := exists_regular_tuple (mem_denseFamily.mp hS) h0
    by_cases havoid : Disjoint sample (tuplePairs f)
    · refine ⟨tupleUnion f,
        Finset.mem_union_right _ (mem_residualFamily.mpr ⟨f, havoid, rfl⟩), ?_⟩
      intro v hv
      obtain ⟨i, hi⟩ := mem_tupleUnion.mp hv
      exact hf i hi
    · obtain ⟨p, hp, hpf⟩ := Finset.not_disjoint_iff.mp havoid
      obtain ⟨i, j, rfl⟩ := mem_tuplePairs.mp hpf
      refine ⟨pairUnion (f.val i, f.val j), ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (mem_sampledFamily.mpr ⟨_, hp, rfl⟩))
      · exact Finset.union_subset (hf i) (hf j)

end TalagrandDiscreteConvexity.Covering

end OAI
