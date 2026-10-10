import OAI.Probability.InvariantIsing.Cavity.CavitySpinPrior
import OAI.Probability.InvariantIsing.Cavity.CavityTiltTransport

namespace OAI

/-! The exact product prior obtained by separating the cavity sites.
The leaf coordinate is preserved by the split. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def cavitySpinSplit (N n : ℕ) : Spin (N + n) ≃ Spin N × Spin n where
  toFun σ := (fun i => σ (Fin.castAdd n i), fun j => σ (Fin.natAdd N j))
  invFun p := Fin.addCases p.1 p.2
  left_inv σ := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    ext i <;> simp

@[simp] lemma cavitySpinSplit_left {N n : ℕ} (σ : Spin (N+n)) (i : Fin N) :
    (cavitySpinSplit N n σ).1 i = σ (Fin.castAdd n i) := rfl

@[simp] lemma cavitySpinSplit_right {N n : ℕ} (σ : Spin (N+n)) (i : Fin n) :
    (cavitySpinSplit N n σ).2 i = σ (Fin.natAdd N i) := rfl

theorem cavity_spin_split_prior (N n : ℕ) :
    MeasurePreserving (cavitySpinSplit N n)
      (uniformSpinPrior (N+n) : Measure (Spin (N+n)))
      ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  have hp : (cavitySpinSplit N n) ⁻¹' {p} = {(cavitySpinSplit N n).symm p} := by
    ext σ
    exact (cavitySpinSplit N n).eq_symm_apply.symm
  rw [hp, ← singleton_prod_singleton, Measure.prod_prod]
  change (PMF.uniformOfFintype (Spin (N+n))).toMeasure {_} =
    (PMF.uniformOfFintype (Spin N)).toMeasure {_} *
      (PMF.uniformOfFintype (Spin n)).toMeasure {_}
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (cavitySpinSplit N n), Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv] <;> simp

def cavitySpinLeafSplit (N n depth : ℕ) :
    Spin (N+n) × LabeledLeaf depth ≃ (Spin N × LabeledLeaf depth) × Spin n where
  toFun p := (((cavitySpinSplit N n p.1).1,p.2),(cavitySpinSplit N n p.1).2)
  invFun p := ((cavitySpinSplit N n).symm (p.1.1,p.2),p.1.2)
  left_inv p := by simp
  right_inv p := by simp

theorem cavity_spin_leaf_split_prior (N n depth : ℕ) (T : LabeledTree depth) :
    MeasurePreserving (cavitySpinLeafSplit N n depth)
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)) := by
  have h := (cavity_spin_split_prior N n).prod
    (MeasurePreserving.id (labeledLeafLaw depth T))
  have hshuffle := measurePreserving_prodAssoc
    (uniformSpinPrior N : Measure (Spin N)) (uniformSpinPrior n : Measure (Spin n))
    (labeledLeafLaw depth T)
  have hswap := (MeasurePreserving.id (uniformSpinPrior N : Measure (Spin N))).prod
    (Measure.measurePreserving_swap (μ := (uniformSpinPrior n : Measure (Spin n)))
      (ν := labeledLeafLaw depth T))
  have hassoc := (measurePreserving_prodAssoc
    (uniformSpinPrior N : Measure (Spin N)) (labeledLeafLaw depth T)
    (uniformSpinPrior n : Measure (Spin n))).symm MeasurableEquiv.prodAssoc
  exact hassoc.comp (hswap.comp (hshuffle.comp h))

end InvariantIsing

end

end OAI
