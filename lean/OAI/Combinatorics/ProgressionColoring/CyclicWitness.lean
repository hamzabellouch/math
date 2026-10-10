import OAI.Combinatorics.ProgressionColoring.CyclicColoring
import OAI.Combinatorics.ProgressionColoring.ConstructionSignatureBudget
import OAI.Combinatorics.ProgressionColoring.OuterDichotomy

namespace OAI

/-!
# The unconditional cyclic two-coloring witness

Every parameter, mesh, literal label, outer coloring, geometric key, and finite
probability budget is supplied by its actual construction theorem. The absolute
threshold is chosen before the prime scale and before any final color count.
-/

noncomputable section

open Filter

namespace QuantitativeVanDerWaerden

open Parameters ConstructionModel SparsePerturbation CyclicColoring

theorem construction_key_fiber_card_le_four {k : ℕ} (s : ConstructionModel.Data k)
    (hk : 3 ≤ k) (hbasic : BasicScales k) :
    ∀ a d : ConstructionModel.Group s, d ≠ 0 →
      ∀ key : (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ,
      (Finset.univ.filter (fun j : Fin k =>
        perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
          (ConstructionModel.lambda k)
          (a + (j.val : ConstructionModel.Group s) * d) = key)).card ≤ 4 := by
  have hunit := ConstructionModel.lambda_coprime s hbasic
  have hunit' : Nat.Coprime (ConstructionModel.lambda k)
      ((s.P ^ s.exponent) ^ dimension k) := by
    simpa only [ConstructionModel.groupSize, s.q_eq_pow] using hunit
  change ∀ a d : CyclicGroup s.q (dimension k), d ≠ 0 →
    ∀ key : (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ,
      (Finset.univ.filter (fun j : Fin k =>
        perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
          (ConstructionModel.lambda k)
          (a + (j.val : CyclicGroup s.q (dimension k)) * d) = key)).card ≤ 4
  rw [s.q_eq_pow]
  intro a d hd key
  exact perturbationKey_fin_fiber_card_le_four (ConstructionModel.mesh s hk)
    s.prime s.prime_lower.le hunit' (ConstructionModel.mesh_small s hk) a d hd key

/-- The eventual construction uses the actual counted outer witness and the
actual rich-or-affine dichotomy, then samples only the finite geometric-key image. -/
theorem eventually_cyclic_coloring :
    ∀ᶠ k : ℕ in atTop, ∃ N : ℕ, 2 ≤ N ∧
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k) ≤ (N : ℝ) ∧
        ∃ C : ZMod N → Bool, CyclicAvoids C k := by
  filter_upwards [ConstructionModel.eventually_outerChoice, eventually_basicScales,
    eventually_geometryScales, ConstructionModel.eventually_outerChoice_sparse_budget]
    with k houter hbasic hgeom hbudget
  obtain ⟨hk, houter⟩ := houter
  let s : ConstructionModel.Data k := ConstructionModel.choose k hk
  let o : ConstructionModel.OuterChoice s hk := Classical.choice (houter s)
  let : NeZero (s.q ^ dimension k) := ConstructionModel.groupSize_neZero s
  let c₀ : ConstructionModel.Group s → Bool :=
    fun n => o.color (ConstructionModel.fullLabel s hk n)
  let key : ConstructionModel.Group s →
      (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ :=
    perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
      (ConstructionModel.lambda k)
  let A := affineProgressions s.q (dimension k) (ConstructionModel.lambda k) k
  have hmult : ∀ ad ∈ nonzeroProgressions (s.q ^ dimension k), ∀ a,
      (Finset.univ.filter (fun j : Fin k => (cyclicSignature c₀ key ad j).2 = a)).card ≤ 4 := by
    intro ad had a
    exact construction_key_fiber_card_le_four s hk hbasic ad.1 ad.2
      ((mem_nonzeroProgressions ad).mp had) a
  have hcases : ∀ ad ∈ nonzeroProgressions (s.q ^ dimension k), ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions (cyclicSignature (k := k) c₀ key ad) b).card := by
    intro ad had
    rcases ConstructionModel.OuterChoice.rich_or_affine s hk o hgeom ad.1 ad.2 with hrich | haff
    · right
      intro b
      refine (hrich (!b)).trans_eq ?_
      apply congrArg (fun n : ℕ => 100 * n)
      apply congrArg (Finset.card : Finset (Fin k) → ℕ)
      apply Finset.ext
      intro j
      constructor
      · intro hj
        apply (@Finset.mem_filter _ _ _ _ _).mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [cyclicSignature, c₀, ConstructionModel.fullLabelWord,
          Bool.eq_not_iff] using ((@Finset.mem_filter _ _ _ _ _).mp hj).2
      · intro hj
        apply (@Finset.mem_filter _ _ _ _ _).mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [cyclicSignature, c₀, ConstructionModel.fullLabelWord,
          Bool.eq_not_iff] using ((@Finset.mem_filter _ _ _ _ _).mp hj).2
    · left
      exact (mem_affineProgressions ad).mpr ⟨(mem_nonzeroProgressions ad).mp had, haff⟩
  have hbudget' : 2 * (((s.q ^ dimension k : ℕ) : ℝ)) ^ 2 *
      flipProbability k ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
    simpa only [A, c₀, key, ConstructionModel.groupSize] using hbudget hk s o
  obtain ⟨C, hC⟩ := exists_cyclicAvoids_of_ambient_keys c₀ key A
    (affineProgressions_subset _ _ _ _) (flipProbability_pos (by omega : 0 < k)).le
    hbasic.flip_small.le hmult hcases hbudget'
  refine ⟨ConstructionModel.groupSize s, ConstructionModel.groupSize_two_le s hk, ?_, C, hC⟩
  simpa only [Parameters.c] using ConstructionModel.groupSize_lower s hk

theorem exists_cyclic_coloring :
    ∃ K : ℕ, ∀ k ≥ K, ∃ N : ℕ, 2 ≤ N ∧
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k) ≤ (N : ℝ) ∧
        ∃ C : ZMod N → Bool, CyclicAvoids C k :=
  eventually_atTop.1 eventually_cyclic_coloring

end QuantitativeVanDerWaerden

end

end OAI
