import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCutoffLaw
import OAI.Probability.InvariantIsing.Cavity.CavityLogCovariance

namespace OAI

/-! The capped logarithmic cavity factor in physical projector
coordinates, including the vanishing quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityProjectorCappedLog {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t cap δ : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (min (t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ * (1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2))
    ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)).tilted (fun x => cavityProjectorHamiltonian p.1 c u z x.1))
    ∂gaussianCoordinates

lemma measurable_cavityProjectorCappedLog {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ} (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (p : Ω → CavityProjectorFrame N m d) (hp : Measurable p) :
    Measurable (fun ω => cavityProjectorCappedLog T c u t cap δ (A ω) (p ω)) := by
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
  let ν : Measure X := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
    (uniformSpinPrior n : Measure (Spin n))
  exact (measurable_random_tilted_integral (ν := fun _ : Ω × (ℕ → ℝ) => ν)
    measurable_const hH hW).log.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem cavity_projector_capped_log {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t cap δ : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d)
    (hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) :
    cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p =
    ∫ z, Real.log (∫ x, Real.exp
      (min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
        δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2))
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x.1)) ∂gaussianCoordinates := by
  let ν := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
    (uniformSpinPrior n : Measure (Spin n))
  let H := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) x.1.1
  let B := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x.1
  let C := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x.1
  let W := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2)
  have he z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityProjectorHamiltonian p.1 (fun a => t*lam a+2*perturbationScale N*v a) u z x.1) =
      fun x => H x+cylinderField (B x) z := by
    funext x
    rw [hp]
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
  unfold cavityProjectorCappedLog
  simp_rw [he]
  exact cavity_log_weight_same_covariance ν H W B C
    (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x.1 y.1)

end InvariantIsing

end

end OAI
