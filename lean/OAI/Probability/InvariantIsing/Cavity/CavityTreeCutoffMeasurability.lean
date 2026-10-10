import OAI.Probability.InvariantIsing.Cavity.CavityRandomPriorCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityFullCutoff

namespace OAI

/-! The original cutoff average is measurable in the actual labeled
tree. The Gaussian and rotation coordinates remain unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_cavityFullCutoffDisorderTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) |
      p.2 ∈ s p.1})
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun T => cavityFullCutoffDisorderTest μ T eig I u s F) := by
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
  have hS : MeasurableSet {p : Ω × X | p.2 ∈ s p.1.1.2} :=
    hs.preimage (measurable_fst.fst.snd.prodMk measurable_snd)
  have hG : Measurable (fun p : Ω × (Fin 2 → X) => F p.1.1.2 p.2) :=
    hF.comp (measurable_fst.fst.snd.prodMk measurable_snd)
  have hh := measurable_random_cavityCutoffReplicaMean ν hν H hH
    (fun p => s p.1.2) hS (fun p => F p.1.1.2 p.2) hG
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

end InvariantIsing

end

end OAI
