import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalCappedLog
import OAI.Probability.InvariantIsing.Cavity.CavityHaarLogObservable
import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalRestrictedLaw

namespace OAI

/-! The actual canonical fresh-group logarithmic observable and its
finite-volume measurability and boundedness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavity_canonical_group_projection_bound {N m d : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (V : Orthogonal N)
    (W : (a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)) (σ : Spin N) :
    ‖cavitySelectedSiteProjection (fun j => (a₀ j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k a₀) (cavityBaseGroupEquiv k e a₀) V)
      (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e a₀ hk) W) σ‖^2 ≤ N := by
  rw [← cavityGroupedSelectedFrame_rotated_coordinates]
  apply cavity_frame_coordinates_norm_le
  apply cavity_orthogonal_frame_gram
  apply cavity_orthogonal_frame_gram
  rw [cavityCanonicalGroupFrame_special, cavityCanonicalSpecial_gram]


def cavityCanonicalHaarLog {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) : ℝ :=
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  cavityHaarLogObservable
    (cavityRotationProbability eig (cavitySpectralGroup (fun i => (E.symm i).1)) u)
    (fun j => (a₀ j,j)) (cavityRotationVectors dims E)
    (cavityCanonicalGroupFrame k e a₀ hk) (fun _ => B) t cap δ p

lemma measurable_cavityCanonicalHaarLog {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n) :
    Measurable (cavityCanonicalHaarLog (depth := depth) k e a₀ hk lam v u t cap δ B) := by
  unfold cavityCanonicalHaarLog
  exact measurable_cavityHaarLogObservable _ (measurable_cavityRotationProbability _ _ _) _ _
    (measurable_cavityRotationVectors _ _) _ _ measurable_const t cap δ

lemma cavityCanonicalHaarLog_bound {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) :
    |cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ B p| ≤
      (|t| *cavityFactorSize B.1 B.2.1 B.2.2+|δ|)*(1+N) := by
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  let ν : Ω → Measure (Spin N × LabeledLeaf depth) :=
    cavityRotationProbability eig (cavitySpectralGroup (fun i => (E.symm i).1)) u
  let vectors := cavityRotationVectors (depth := depth) dims E
  let frames := cavityCanonicalGroupFrame k e a₀ hk
  have hy (ω : Ω) (W : (a : Fin m) → Orthogonal (dims a)) (x : Spin N × LabeledLeaf depth) :
      ‖cavitySelectedSiteProjection (fun j => (a₀ j,j)) (vectors ω)
        (cavityGroupHaarFrames frames W) x‖^2 ≤ (N : ℝ) := by
    change ‖cavitySelectedSiteProjection (fun j => (a₀ j,j))
      (cavityGroupSpinCoordinates dims E ω.1.1) (cavityGroupHaarFrames frames W) x.1‖^2 ≤ N
    exact cavity_canonical_group_projection_bound k e a₀ hk ω.1.1 W x.1
  exact cavityHaarLogObservable_bound ν (fun j => (a₀ j,j)) vectors frames (fun _ => B)
    t cap δ hcap (fun _ => le_rfl) hy p

end InvariantIsing

end

end OAI
