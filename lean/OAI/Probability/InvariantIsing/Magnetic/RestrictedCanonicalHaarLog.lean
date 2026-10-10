import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalHaarLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarLogObservable
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationProbability

namespace OAI

/-! The constrained base Gibbs law and independent fresh group frames
in the actual canonical capped logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def restrictedCanonicalHaarLog {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) : ℝ :=
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  restrictedHaarLogObservable C hC
    (restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u)
    (fun j => (a₀ j,j)) (cavityRotationVectors dims E)
    (cavityCanonicalGroupFrame k e a₀ hk) (fun _ => B) t cap δ p

lemma measurable_restrictedCanonicalHaarLog {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n) :
    Measurable (restrictedCanonicalHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ B) := by
  unfold restrictedCanonicalHaarLog
  exact measurable_restrictedHaarLogObservable C hC _ (measurable_restrictedRotationProbability S hS _ _ _) _ _
    (measurable_cavityRotationVectors _ _) _ _ measurable_const t cap δ

lemma restrictedCanonicalHaarLog_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) :
    |restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ B p| ≤
      (|t| *cavityFactorSize B.1 B.2.1 B.2.2+|δ|)*(1+N) := by
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  let ν : Ω → Measure (Spin N × LabeledLeaf depth) :=
    restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u
  let vectors := cavityRotationVectors (depth := depth) dims E
  let frames := cavityCanonicalGroupFrame k e a₀ hk
  have hy (ω : Ω) (W : (a : Fin m) → Orthogonal (dims a)) (x : Spin N × LabeledLeaf depth) :
      ‖cavitySelectedSiteProjection (fun j => (a₀ j,j)) (vectors ω)
        (cavityGroupHaarFrames frames W) x‖^2 ≤ (N : ℝ) := by
    change ‖cavitySelectedSiteProjection (fun j => (a₀ j,j))
      (cavityGroupSpinCoordinates dims E ω.1.1) (cavityGroupHaarFrames frames W) x.1‖^2 ≤ N
    exact cavity_canonical_group_projection_bound k e a₀ hk ω.1.1 W x.1
  exact restrictedHaarLogObservable_bound C hC ν (fun j => (a₀ j,j)) vectors frames (fun _ => B)
    t cap δ hcap (fun _ => le_rfl) hy p

end InvariantIsing

end

end OAI
