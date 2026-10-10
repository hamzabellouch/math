import OAI.Probability.InvariantIsing.Cavity.CavityTreeCutoffMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityFullSiteIdentity
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTotalBound

namespace OAI

/-! Bounded full and restricted Gibbs tests can be averaged over the
original labeled-tree law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityFullTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun T => cavityFullTest μ T eig I u F) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.fst
  let H : Ω × X → ℝ := fun p => cavityFullHamiltonian eig I u (p.1.1.2,p.1.2) p.2
  have hH : Measurable H := by
    have hp : Measurable (fun p : Ω × X => ((p.1.1.2,p.1.2),p.2)) :=
      (measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd
    exact Measurable.comp
      (g := Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u))
      (f := fun p : Ω × X => ((p.1.1.2,p.1.2),p.2))
      (measurable_cavityFullHamiltonian eig I u) hp
  have hh := measurable_random_referenceReplicaMean hν hH
    (D := fun p => F p.2) ((measurable_of_countable F).comp measurable_snd)
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

lemma cavityFullCutoffDisorderTest_abs_le {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig I u s F| ≤ M := by
  have hi U : ‖∫ z, cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) ∂gaussianCoordinates‖ ≤ M := by
    have hh := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
      (f := fun z => cavityCutoffReplicaMean
        (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
        (cavityFullHamiltonian eig I u (U,z)) (s U) (F U))
      (C := M) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using cavity_cutoff_replica_abs_le_all
          (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
          (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) hM (hF U))
    simpa only [probReal_univ,mul_one] using hh
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => ∫ z, cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) ∂gaussianCoordinates)
    (C := M) (ae_of_all _ hi)
  simpa only [cavityFullCutoffDisorderTest,Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
