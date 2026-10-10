import OAI.NumberTheory.DukePrimeDegree.Dynamics.NoCentralizerOrbit

namespace OAI

/-!
# An explicit neutral direction excluding centralizer orbits

The two root coordinates receive the same negative weight. The remaining
coordinates receive distinct positive weights. Their sum is balanced by
the repeated negative weight. This discharges the elementary weight
conditions in the centralizer-orbit exclusion.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def centralizerWitnessWeights {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) : Fin n → ℝ :=
  fun i => Sum.elim (fun _ : Fin 2 => -(∑ r : Fin m, ((r : ℝ) + 1)) / 2)
    (fun r : Fin m => (r : ℝ) + 1) (e i)

lemma centralizerWitnessWeights_sum {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    ∑ i, centralizerWitnessWeights e i = 0 := by
  unfold centralizerWitnessWeights
  rw [e.sum_comp, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma centralizerWitnessWeights_neutral {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    centralizerWitnessWeights e (e.symm (Sum.inl 0)) =
      centralizerWitnessWeights e (e.symm (Sum.inl 1)) := by
  simp [centralizerWitnessWeights]

lemma centralizerWitnessWeights_negative {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hm : 0 < m) : centralizerWitnessWeights e (e.symm (Sum.inl 0)) < 0 := by
  have hs : 0 < ∑ r : Fin m, ((r : ℝ) + 1) := by
    apply Finset.sum_pos'
    · intro r _
      positivity
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, by norm_num⟩
  simp only [centralizerWitnessWeights, Equiv.apply_symm_apply, Sum.elim_inl]
  linarith

lemma centralizerWitnessWeights_injective {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    Function.Injective (fun r : Fin m => centralizerWitnessWeights e (e.symm (Sum.inr r))) := by
  intro r s h
  simp only [centralizerWitnessWeights, Equiv.apply_symm_apply, Sum.elim_inr] at h
  have hval : (r : ℝ) = (s : ℝ) := add_right_cancel h
  apply Fin.ext
  exact_mod_cast hval

/-- No nonzero finite measure invariant under the neutral diagonal group
can be supported on a single root-pair centralizer orbit. -/
theorem no_invariant_rootPair_orbit {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m) (hm : 0 < m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : ∀ (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0),
      ell (e.symm (Sum.inl 0)) = ell (e.symm (Sum.inl 1)) →
      μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) : False := by
  exact no_invariant_rootPair_orbit_of_weights e hij (centralizerWitnessWeights e)
    (centralizerWitnessWeights_sum e) (centralizerWitnessWeights_neutral e)
    (centralizerWitnessWeights_negative e hm) (centralizerWitnessWeights_injective e)
    μ x hfull (hinv _ _ (centralizerWitnessWeights_neutral e))

end DukePrimeDegree

end

end OAI
