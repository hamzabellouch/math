import OAI.Probability.InvariantIsing.Cavity.CavityProjectorLog
import OAI.Probability.InvariantIsing.Cavity.CavityRotationLogMean
import OAI.Probability.InvariantIsing.Cavity.CavityRotationProbability

namespace OAI

/-! Joint measurability of the actual logarithms when the finite cascade
is randomized. This permits averaging the physical increment over trees. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityProjectorCappedLog_tree {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ} (T : Ω → LabeledTree depth) (hT : Measurable T) (c : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (p : Ω → CavityProjectorFrame N m d) (hp : Measurable p) :
    Measurable (fun ω => cavityProjectorCappedLog (T ω) c u t cap δ (A ω) (p ω)) := by
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let H := fun q : (Ω × (ℕ → ℝ)) × X =>
    cavityProjectorHamiltonian (p q.1.1).1 c u q.1.2 q.2.1
  let W := fun q : (Ω × (ℕ → ℝ)) × X => Real.exp
    (min (t*cavityLogFactor (A q.1.1).1 (A q.1.1).2.1 (A q.1.1).2.2
      (cavityFrameCoordinates (p q.1.1).2 q.2.1.1) q.2.2) cap -
        δ*(1+‖cavityFrameCoordinates (p q.1.1).2 q.2.1.1‖^2))
  have hH : Measurable H := by
    dsimp only [H]
    let π : (Ω × (ℕ → ℝ)) × X →
        (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) := fun q => (q.1,q.2.1)
    have hπ : Measurable π := measurable_fst.prodMk measurable_snd.fst
    have hb := measurable_cavityProjectorHamiltonian_pullback
      (N := N) (m := m) (depth := depth) (fun ω => (p ω).1) hp.fst c u
    have hh := hb.comp hπ
    simpa only [Function.comp_def, π] using hh
  have hW : Measurable W := by
    apply measurable_from_prod_countable_left
    intro x
    have hy : Measurable (fun q : Ω × (ℕ → ℝ) =>
        cavityFrameCoordinates (p q.1).2 x.1.1) :=
      ((continuous_cavityFrameCoordinates x.1.1).measurable.comp hp.snd).comp measurable_fst
    have hb : Measurable (fun q : Ω × (ℕ → ℝ) =>
        cavityLogFactor (A q.1).1 (A q.1).2.1 (A q.1).2.2
          (cavityFrameCoordinates (p q.1).2 x.1.1) x.2) :=
      (measurable_cavityBlockPotential A hA (fun ω => (p ω).2) hp.snd x.1.1 x.2).comp
        measurable_fst
    exact (((hb.const_mul t).min measurable_const).sub
      ((measurable_const.add (hy.norm.pow_const 2)).const_mul δ)).exp
  let ν₀ : Ω × (ℕ → ℝ) → Measure (Spin N × LabeledLeaf depth) := fun q =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) (T q.1)
  have hν₀ : Measurable ν₀ :=
    (measurable_labeledSpinReference_general depth (uniformSpinPrior N : Measure (Spin N))).comp
      (hT.comp measurable_fst)
  let κ : Kernel (Ω × (ℕ → ℝ)) (Spin N × LabeledLeaf depth) := Kernel.mk ν₀ hν₀
  let : IsMarkovKernel κ := ⟨fun q => inferInstanceAs (IsProbabilityMeasure (ν₀ q))⟩
  have hν : Measurable (fun q => (ν₀ q).prod (uniformSpinPrior n : Measure (Spin n))) := by
    have hh : Measurable (fun q => (κ.prod (Kernel.const (Ω × (ℕ → ℝ))
      (uniformSpinPrior n : Measure (Spin n)))) q) :=
        (κ.prod (Kernel.const (Ω × (ℕ → ℝ)) (uniformSpinPrior n : Measure (Spin n)))).measurable
    simpa only [Kernel.prod_apply, Kernel.const_apply, Kernel.coe_mk, κ] using hh
  exact (measurable_random_tilted_integral
    (ν := fun q => (ν₀ q).prod (uniformSpinPrior n : Measure (Spin n)))
    hν hH hW).log.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

lemma measurable_cavityRotationLogMean_tree {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (fun q : Orthogonal N × LabeledTree depth =>
      cavityRotationLogMean q.2 eig I u q.1) := by
  let ν : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ) →
      Measure (Spin N × LabeledLeaf depth) := fun q =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) q.1.2
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.snd
  exact (measurable_random_referencePartition hν
    (measurable_cavityRotationProbabilityHamiltonian eig I u)).log.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

lemma integrable_cavityRotationLogMean_tree {N m depth : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) :
    Integrable (fun q : Orthogonal N × LabeledTree depth =>
      cavityRotationLogMean q.2 eig I u q.1) (μ.prod θ) := by
  apply Integrable.of_bound
    (measurable_cavityRotationLogMean_tree eig I u).aestronglyMeasurable
    (1+2*((∑ i, |eig i|)*N/2)^2+8*Real.exp (2*(4*(N*perturbationScale N^2))))
  exact ae_of_all _ fun q => by
    rw [Real.norm_eq_abs]
    exact cavityRotationLogMean_bound q.2 eig I u hu q.1

end InvariantIsing

end

end OAI
