import OAI.Probability.InvariantIsing.Cavity.CavityBaseGroups
import OAI.Probability.InvariantIsing.Cavity.CavityGroupedWeightedAverage

namespace OAI

/-! The actual canonical cavity frame admits the fresh-group Gibbs
representation. No new independent-frame assumption is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityCanonicalGroupFrame {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    (a : Fin m) → Matrix (Fin (cavityBaseGroupDimension k g a)) (Fin d) ℝ :=
  Classical.choose (cavity_canonical_group_frames k e g hk)

lemma cavityCanonicalGroupFrame_gram {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (a : Fin m) :
    (cavityCanonicalGroupFrame k e g hk a).transpose*cavityCanonicalGroupFrame k e g hk a=1 :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).1 a

lemma cavityCanonicalGroupFrame_special {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
      (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)=cavityCanonicalSpecial e :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).2

lemma cavityCanonicalProjectorFrame_grouped {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (V : Orthogonal N) :
    cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e g) =
    (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv k e g).symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
          (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)) := by
  apply Prod.ext
  · rw [cavityCanonicalProjectorFrame_action_fst]
    funext a
    congr 1
    ext i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
      cavityBaseGroupEquiv_label]
  · rw [cavityCanonicalGroupFrame_special]
    rfl

theorem cavity_canonical_weighted_average {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e g)) ∂μ) =
    let E := cavityBaseGroupEquiv k e g
    let A := cavityCanonicalGroupFrame k e g hk
    ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
            (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (uniformSpinPrior n))
      ({x | 1+‖cavitySelectedSiteProjection (fun j => (g j,j))
        (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
          Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
            (cavitySelectedSiteProjection (fun j => (g j,j))
              (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
              (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ := by
  simp_rw [cavityCanonicalProjectorFrame_grouped k e g hk]
  exact cavity_grouped_weighted_average (cavityBaseGroupDimension k g)
    (cavityBaseGroupEquiv k e g) (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)
    μ η T lam v u hu t D B F hM hF

end InvariantIsing

end

end OAI
