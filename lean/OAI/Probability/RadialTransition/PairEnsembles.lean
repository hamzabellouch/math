import OAI.Probability.RadialTransition.MeasurableEnergy

namespace OAI

universe uX uY uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section MeasurablePairs
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

lemma measurable_pairWithin (v : X → X → ℝ)
    (hv : Measurable (Function.uncurry v)) : Measurable (pairWithin v) := by
  apply measurable_particle_iff.mpr
  intro n
  change Measurable (fun a : Fin n → X => (1/2:ℝ) *
    ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else v (a i) (a j))
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : i = j
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]
    exact hv.comp (show Measurable (fun a : Fin n → X => (a i, a j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma measurable_pairBetween (v : X → Y → ℝ)
    (hv : Measurable (Function.uncurry v)) : Measurable (Function.uncurry (pairBetween v)) := by
  apply measurable_particle_prod
  intro m n
  change Measurable (fun p : (Fin m → X) × (Fin n → Y) =>
    ∑ i : Fin m, ∑ j : Fin n, v (p.1 i) (p.2 j))
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    hv.comp (show Measurable (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j)) from
      ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))))

end MeasurablePairs
section MeasurablePairCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

lemma measurable_pairCellEnergy (v : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Measurable (Function.uncurry (v i j))) : Measurable (pairCellEnergy v) := by
  unfold pairCellEnergy cellHamiltonian
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun i _ => (measurable_pairWithin _ (hv i i)).comp (measurable_pi_apply i))
  · apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    by_cases h : i = j
    · simp only [h, ite_true]; exact measurable_const
    · simp only [h, ite_false]
      exact (measurable_pairBetween _ (hv i j)).comp
        (show Measurable (fun a : ∀ k, ParticleState (X k) => (a i, a j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))

omit [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)] in
lemma pairCellEnergy_no_cross (v : ∀ i j, X i → X j → ℝ)
    (hcross : ∀ i j, i ≠ j → ∀ x y, v i j x y = 0) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy v x = ∑ i, pairWithin (v i i) (x i) := by
  unfold pairCellEnergy cellHamiltonian
  have hz (i j : I) : (if i = j then 0 else pairBetween (v i j) (x i) (x j)) = 0 := by
    split_ifs with h
    · rfl
    · simp [pairBetween, hcross i j h]
  simp only [hz, Finset.sum_const_zero, mul_zero, add_zero]

lemma boltzmannPartition_no_cross (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (v : ∀ i j, X i → X j → ℝ)
    (hcross : ∀ i j, i ≠ j → ∀ x y, v i j x y = 0) (β z : ℝ) :
    boltzmannPartition (Measure.pi (fun i => particleBase (ν i) z)) (fun x => β * pairCellEnergy v x) =
      ∏ i, boltzmannPartition (particleBase (ν i) z) (fun x => β * pairWithin (v i i) x) := by
  unfold boltzmannPartition
  simp_rw [pairCellEnergy_no_cross v hcross, ← neg_mul, Finset.mul_sum, Real.exp_sum]
  exact integral_fintype_prod_eq_prod (fun i (x : ParticleState (X i)) =>
    Real.exp (-β * pairWithin (v i i) x))

end MeasurablePairCells

section GeneralGrand
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

def pairGrand (v : X → X → ℝ) (μ : Measure X) (β z : ℝ) : ℝ :=
  ∫ x, Real.exp (-β * multisetEnergy v (particleMultiset x)) ∂particleBase μ z

lemma pairGrand_eq_cell {I : Type} [Fintype I] [DecidableEq I]
    (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, Y i → X) (hpos : ∀ i, Measurable (pos i))
    (v : X → X → ℝ) (hv : Measurable (Function.uncurry v)) (hsym : ∀ x y, v x y = v y x)
    {μ : Measure X} (hdecomp : μ = ∑ i, Measure.map (pos i) (ν i)) (β z : ℝ) :
    pairGrand v μ β z = boltzmannPartition (Measure.pi (fun i => particleBase (ν i) z))
      (fun x => β * pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x) := by
  have hcfg := measurableConfiguration_boltzmann hv hsym β
  have hleft : Measurable (fun x : ParticleState X => Real.exp (-β * multisetEnergy v (particleMultiset x))) := by
    apply measurable_particle_iff.mpr
    intro n
    exact Real.measurable_exp.comp (measurable_const.mul (measurable_multisetEnergy_configuration hv))
  have hright : Measurable (fun x : ∀ i, ParticleState (Y i) =>
      Real.exp (-(β * pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x))) := by
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply measurable_const.mul
    apply measurable_pairCellEnergy
    intro i j
    exact hv.comp (((hpos i).comp measurable_fst).prodMk ((hpos j).comp measurable_snd))
  rw [pairGrand, boltzmannPartition,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hleft.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hright.aestronglyMeasurable]
  congr 1
  have hh := particleBase_sum_map_observable_meas Y
    (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy v s))) hcfg ν pos hpos z 0
  simp only [zero_add, multisetEnergy_mappedMulti] at hh
  simpa only [hdecomp, neg_mul] using hh

end GeneralGrand

lemma pairGrand_radial {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hs : StableWith φ B) (hβ : 0 ≤ β) {A : Set Position}
    (hAfin : volume A ≠ ⊤) (z : ℝ) :
    pairGrand (radialPair φ) (volume.restrict A) β z = grandOn φ A β z := by
  have hm : Measurable (fun x : ParticleState Position => Real.exp (-β * multisetEnergy (radialPair φ) (particleMultiset x))) := by
    simpa only [multisetEnergy_radial] using measurable_particleBoltzmann hφ β
  rw [pairGrand, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hm.aestronglyMeasurable]
  simp only [multisetEnergy_radial]
  rw [lintegral_grandOn hφ hb hs hβ hAfin z,
    ENNReal.toReal_ofReal (zero_le_one.trans (grandOn_bounds hφ hb hs hβ hAfin z).1)]

end RadialTransition

end

end OAI
