import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLayoutExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParameterPreparation

namespace OAI

/-! # Preparing stored layout data and prime widths after the bounded draw -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationLayoutPreparation

variable {n : ℕ}

structure Data (n : ℕ) where
  permutation : Vector (Fin n) n
  signs : IndexedMask n
  domains : Vector (List (Fin n)) 3
  parameters : MixerParameterExecution.Parameters

def run (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed) :
    Option (Data n) × ℕ :=
  let layout := RepresentationLayoutExecution.run D.zeroSetup s
  match layout.1 with
  | none => (none, layout.2 + 1)
  | some (v, signs) =>
    let prepared := RepresentationParameterPreparation.run D v
    (some ⟨v, signs, prepared.1.1, prepared.1.2⟩, layout.2 + prepared.2 + 1)

theorem prepared (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed)
    (data : Data n) (h : (run D s).1 = some data) :
    (data.domains, data.parameters) =
      (RepresentationParameterPreparation.run D data.permutation).1 := by
  unfold run at h
  cases hl : (RepresentationLayoutExecution.run D.zeroSetup s).1 with
  | none => simp only [hl, reduceCtorEq] at h
  | some pair =>
    rcases pair with ⟨v, signs⟩
    simp only [hl, Option.some.injEq] at h
    subst data
    rfl

theorem value (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed)
    (data : Data n) (h : (run D s).1 = some data) :
    ∃ e, D.zeroSetup.layoutCoupling.bounded s = some (e, data.signs.semantic) ∧
      (∀ i : Fin n, data.permutation[i.val] = e i) ∧
      (∀ j : Fin 3, data.domains[j.val] = (permuteSubset e (D.mixers j)).sort (· ≤ ·)) ∧
      (∀ j : Fin 4, data.parameters.widths[j.val] =
        D.zeroSetup.samplerPrimeWidths (e, data.signs.semantic) j) := by
  unfold run at h
  cases hl : (RepresentationLayoutExecution.run D.zeroSetup s).1 with
  | none => simp only [hl, reduceCtorEq] at h
  | some pair =>
    rcases pair with ⟨v, signs⟩
    simp only [hl, Option.some.injEq] at h
    subst data
    obtain ⟨e, he, hv⟩ := RepresentationLayoutExecution.value D.zeroSetup s v signs hl
    refine ⟨e, he, hv, ?_, ?_⟩
    · intro j
      exact RepresentationMixerPreparation.domains_value D v e hv j
    · intro j
      exact RepresentationParameterPreparation.widths_value D v e hv signs.semantic j

theorem complete (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed)
    (e : Equiv.Perm (Fin n)) (signs : Finset (Fin n))
    (h : D.zeroSetup.layoutCoupling.bounded s = some (e, signs)) :
    ∃ data, (run D s).1 = some data ∧ data.signs.semantic = signs := by
  obtain ⟨v, mask, hv, hm, _⟩ := RepresentationLayoutExecution.complete D.zeroSetup s e signs h
  refine ⟨⟨v, mask, (RepresentationParameterPreparation.run D v).1.1,
    (RepresentationParameterPreparation.run D v).1.2⟩, ?_, hm⟩
  simp only [run, hv]

theorem work (D : RepresentationData n) (hn : 10000 ≤ n)
    (s : D.zeroSetup.layoutCoupling.Seed) :
    (run D s).2 ≤ n * n ^ 3 + 10 * (n + 1) ^ 2 + 4 * n + 6 +
      inputScale D.input ^ 6 * 2 ^ mixerSize n := by
  have hw := RepresentationLayoutExecution.work D.zeroSetup s
  unfold run
  cases hl : (RepresentationLayoutExecution.run D.zeroSetup s).1 with
  | none => simp only [hl]; omega
  | some pair =>
    rcases pair with ⟨v, signs⟩
    obtain ⟨e, _, hv⟩ := RepresentationLayoutExecution.value D.zeroSetup s v signs hl
    have hp := RepresentationParameterPreparation.work D hn v e hv
    simp only [hl]
    omega

end LowSpaceSubsetSum.RepresentationLayoutPreparation

end

end OAI
