import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior

namespace OAI

/-! Exact product decomposition for constrained cavity blocks. The
normalization cost is the sum of the two original cube-mass costs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def cavityProductSlice {N n : ℕ} (S : Finset (Spin N)) (T : Finset (Spin n)) :
    Finset (Spin (N+n)) :=
  (S ×ˢ T).map (cavitySpinSplit N n).symm.toEmbedding

lemma mem_cavityProductSlice {N n : ℕ} (S : Finset (Spin N)) (T : Finset (Spin n))
    (σ : Spin (N+n)) : σ ∈ cavityProductSlice S T ↔
      (cavitySpinSplit N n σ).1 ∈ S ∧ (cavitySpinSplit N n σ).2 ∈ T := by
  simp [cavityProductSlice]

lemma cavityProductSlice_card {N n : ℕ} (S : Finset (Spin N)) (T : Finset (Spin n)) :
    (cavityProductSlice S T).card = S.card * T.card := by
  simp [cavityProductSlice]

lemma cavityProductSlice_nonempty {N n : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (T : Finset (Spin n)) (hT : T.Nonempty) : (cavityProductSlice S T).Nonempty := by
  obtain ⟨σ,hσ⟩ := hS
  obtain ⟨τ,hτ⟩ := hT
  refine ⟨(cavitySpinSplit N n).symm (σ,τ), ?_⟩
  rw [mem_cavityProductSlice]
  simpa using And.intro hσ hτ

lemma cavityProductSlice_log_mass {N n : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (T : Finset (Spin n)) (hT : T.Nonempty) :
    Real.log (cavityProductSlice S T).card - (N+n) * Real.log 2 =
      (Real.log S.card - N * Real.log 2) + (Real.log T.card - n * Real.log 2) := by
  rw [cavityProductSlice_card, Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr hS.card_pos.ne') (Nat.cast_ne_zero.mpr hT.card_pos.ne')]
  ring

theorem restricted_cavity_spin_split_prior {N n : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (T : Finset (Spin n)) (hT : T.Nonempty) :
    MeasurePreserving (cavitySpinSplit N n)
      (restrictedSpinPrior (cavityProductSlice S T) (cavityProductSlice_nonempty S hS T hT) :
        Measure (Spin (N+n)))
      ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior T hT)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro p
  let μ := (restrictedSpinPrior (cavityProductSlice S T)
    (cavityProductSlice_nonempty S hS T hT) : Measure (Spin (N+n)))
  have hp : (cavitySpinSplit N n) ⁻¹' {p} = {(cavitySpinSplit N n).symm p} := by
    ext σ
    exact (cavitySpinSplit N n).eq_symm_apply.symm
  have he : (μ.map (cavitySpinSplit N n)).real {p} =
      ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior T hT)).real {p} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p), hp]
    change μ.real {(cavitySpinSplit N n).symm p} = _
    rw [restrictedSpinPrior_singleton, measureReal_def,
      ← singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
    change _ = (restrictedSpinPrior S hS : Measure (Spin N)).real {p.1} *
      (restrictedSpinPrior T hT : Measure (Spin n)).real {p.2}
    rw [restrictedSpinPrior_singleton, restrictedSpinPrior_singleton]
    simp only [mem_cavityProductSlice, Equiv.apply_symm_apply, cavityProductSlice_card, Nat.cast_mul]
    by_cases h₁ : p.1 ∈ S <;> by_cases h₂ : p.2 ∈ T <;> simp [h₁, h₂, mul_comm]
  have hh := congrArg ENNReal.ofReal he
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

theorem restricted_cavity_spin_leaf_split_prior {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (T : LabeledTree depth) :
    MeasurePreserving (cavitySpinLeafSplit N n depth)
      (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C)
        (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T)
      ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
        (restrictedSpinPrior C hC)) := by
  have h := (restricted_cavity_spin_split_prior S hS C hC).prod
    (MeasurePreserving.id (labeledLeafLaw depth T))
  have hshuffle := measurePreserving_prodAssoc
    (restrictedSpinPrior S hS : Measure (Spin N)) (restrictedSpinPrior C hC : Measure (Spin n))
    (labeledLeafLaw depth T)
  have hswap := (MeasurePreserving.id (restrictedSpinPrior S hS : Measure (Spin N))).prod
    (Measure.measurePreserving_swap (μ := (restrictedSpinPrior C hC : Measure (Spin n)))
      (ν := labeledLeafLaw depth T))
  have hassoc := (measurePreserving_prodAssoc
    (restrictedSpinPrior S hS : Measure (Spin N)) (labeledLeafLaw depth T)
    (restrictedSpinPrior C hC : Measure (Spin n))).symm MeasurableEquiv.prodAssoc
  exact hassoc.comp (hswap.comp (hshuffle.comp h))

end InvariantIsing

end

end OAI
