import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTest
import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTail
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTotalBound
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalFactor
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProductPrior

namespace OAI

/-! The actual original-spin geometric cutoff as a measurable bounded
function of its orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def restrictedOriginalGeometricMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (U : SpecialOrthogonal (N+n)) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates

lemma measurable_restrictedOriginalGeometricMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (T : LabeledTree depth) (eig : Fin (N+n) → ℝ)
    (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    Measurable (restrictedOriginalGeometricMean S hS Cset hCset g B T eig u D F) := by
  let X := Spin (N+n) × LabeledLeaf depth
  let I := cavitySpectralGroup g
  have hO : Measurable (cavitySpecialOrthogonal (N := N+n)) :=
    measurable_subtype_coe.subtype_mk
  have hBc := hB.comp ((measurable_cavityCompressionGrams g).comp hO)
  have hs : MeasurableSet {q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × X |
      cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1.1)))
        q.1.1 (cavitySpinSplit N n q.2.1) ≤ D} := by
    apply measurableSet_le _ measurable_const
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityFullSpecialCoordinates g _ hBc
      (cavityJoinedSpin (cavitySpinSplit N n x.1))).norm.pow_const 2).const_add 1 |>.comp
        measurable_fst
  have hH := measurable_cavityFullHamiltonian (N := N+n) (m := m) (depth := depth) eig I u
  have hF : Measurable (fun q : (SpecialOrthogonal (N+n) × (ℕ → ℝ)) × (Fin 2 → X) =>
      F (fun i => (cavitySpinSplit N n (q.2 i).1,(q.2 i).2))) := by
    have hf : Measurable (fun σ : Fin 2 → X =>
        F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) := measurable_of_countable _
    exact hf.comp measurable_snd
  have hc := measurable_cavityCutoffReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) hH
    (fun q => {x | cavityGeometricWeight g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal q.1))) q.1
        (cavitySpinSplit N n x.1) ≤ D}) hs _ hF
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

lemma restrictedOriginalGeometricMean_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (U : SpecialOrthogonal (N+n)) :
    ‖restrictedOriginalGeometricMean S hS Cset hCset g B T eig u D F U‖ ≤ M := by
  have hb := fun z => cavity_cutoff_replica_abs_le_all
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) hM (fun σ => hF _)
  have ht := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
    (f := fun z => cavityCutoffReplicaMean
      (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
      (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
      {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavitySpinSplit N n x.1) ≤ D}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))))
    (C := M) (ae_of_all gaussianCoordinates (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  simpa only [restrictedOriginalGeometricMean, probReal_univ, mul_one] using ht

end InvariantIsing

end

end OAI
