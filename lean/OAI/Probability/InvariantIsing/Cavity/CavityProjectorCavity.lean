import OAI.Probability.InvariantIsing.Cavity.CavityProjectorMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactors
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTotalBound

namespace OAI

/-! The normalized cavity observable as a measurable function of the
physical labeled projectors, selected frame and small coefficient blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityFrameCoordinates {N d : ℕ} (S : Matrix (Fin N) (Fin d) ℝ)
    (σ : Spin N) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (S.transpose *ᵥ (fun i => spinValue (σ i)))

lemma continuous_cavityFrameCoordinates {N d : ℕ} (σ : Spin N) :
    Continuous (fun S : Matrix (Fin N) (Fin d) ℝ => cavityFrameCoordinates S σ) := by
  unfold cavityFrameCoordinates
  fun_prop

lemma measurable_cavityBlockPotential {Ω : Type*} [MeasurableSpace Ω] {N n d : ℕ}
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (S : Ω → Matrix (Fin N) (Fin d) ℝ) (hS : Measurable S)
    (σ : Spin N) (ε : Spin n) :
    Measurable (fun ω => cavityLogFactor (A ω).1 (A ω).2.1 (A ω).2.2
      (cavityFrameCoordinates (S ω) σ) ε) := by
  have hy := (continuous_cavityFrameCoordinates σ).measurable.comp hS
  unfold cavityLogFactor cavityQuadratic
  fun_prop

def cavityProjectorCavityMean {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n))
    (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
      t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
    {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F ∂gaussianCoordinates

lemma cavityProjectorCavityMean_bound {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ σ, |F σ| ≤ C)
    (p : CavityProjectorFrame N m d) :
    ‖cavityProjectorCavityMean T c u t D A F p‖ ≤ C := by
  have hb : ∀ᵐ z ∂gaussianCoordinates, ‖cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
        t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
      {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F‖ ≤ C := by
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact cavity_cutoff_replica_abs_le_all _ _ _ _ hC hF
  simpa only [cavityProjectorCavityMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma measurable_cavityProjectorCavityMean {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ} (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (p : Ω → CavityProjectorFrame N m d) (hp : Measurable p)
    (F : Ω → (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun ω => cavityProjectorCavityMean T c u t D (A ω) (F ω) (p ω)) := by
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let H := fun q : (Ω × (ℕ → ℝ)) × X =>
    cavityProjectorHamiltonian (p q.1.1).1 c u q.1.2 q.2.1 +
      t*cavityLogFactor (A q.1.1).1 (A q.1.1).2.1 (A q.1.1).2.2
        (cavityFrameCoordinates (p q.1.1).2 q.2.1.1) q.2.2
  have hH : Measurable H := by
    let π : (Ω × (ℕ → ℝ)) × X →
        (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) := fun q => (q.1,q.2.1)
    have hπ : Measurable π := measurable_fst.prodMk measurable_snd.fst
    have hb := measurable_cavityProjectorHamiltonian_pullback
      (N := N) (m := m) (depth := depth) (fun ω => (p ω).1) hp.fst c u
    have hg := hb.comp hπ
    apply Measurable.add hg
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityBlockPotential A hA (fun ω => (p ω).2) hp.snd x.1.1 x.2).comp
      measurable_fst).const_mul t
  have hs : MeasurableSet {q : (Ω × (ℕ → ℝ)) × X |
      1 + ‖cavityFrameCoordinates (p q.1.1).2 q.2.1.1‖^2 ≤ D} := by
    have hy : Measurable (fun q : (Ω × (ℕ → ℝ)) × X =>
        cavityFrameCoordinates (p q.1.1).2 q.2.1.1) := by
      apply measurable_from_prod_countable_left
      intro x
      exact ((continuous_cavityFrameCoordinates x.1.1).measurable.comp hp.snd).comp
        measurable_fst
    exact measurableSet_le (measurable_const.add (hy.norm.pow_const 2)) measurable_const
  have hG := measurable_cavityCutoffReplicaMean
    ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)) H hH
    (fun q => {x | 1 + ‖cavityFrameCoordinates (p q.1).2 x.1.1‖^2 ≤ D}) hs
    (fun q => F q.1.1 q.2) (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
