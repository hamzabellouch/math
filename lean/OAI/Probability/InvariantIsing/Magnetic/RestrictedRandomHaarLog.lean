import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalHaarLog

namespace OAI

/-! The canonical logarithm with independent random compression
coefficients. The original base disorder stays in its own coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRandomHaarLog {Z : Type*} {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Z → CavityFactorBlocks d n)
    (p : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a))) : ℝ :=
  restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ (A p.1.1) (p.1.2,p.2)

lemma measurable_restrictedRandomHaarLog {Z : Type*} [MeasurableSpace Z] {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Z → CavityFactorBlocks d n) (hA : Measurable A) :
    Measurable (restrictedRandomHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ A) := by
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let Ω := Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  let ν : Ω → Measure (Spin N × LabeledLeaf depth) := fun z =>
    restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u z.2
  let vectors := fun z : Ω => cavityRotationVectors (depth := depth) dims E z.2
  have hmν : Measurable ν := (measurable_restrictedRotationProbability S hS _ _ _).comp measurable_snd
  have hmv x : Measurable (fun z a => vectors z a x) :=
    (measurable_cavityRotationVectors dims E x).comp measurable_snd
  exact measurable_restrictedHaarLogObservable C hC ν hmν (fun j => (a₀ j,j)) vectors hmv
    (cavityCanonicalGroupFrame k e a₀ hk) (fun z => A z.1) (hA.comp measurable_fst) t cap δ

lemma restrictedRandomHaarLog_bound {Z : Type*} {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : Z → CavityFactorBlocks d n) {D : ℝ}
    (hA : ∀ z, cavityFactorSize (A z).1 (A z).2.1 (A z).2.2 ≤ D)
    (p : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a))) :
    |restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ A p| ≤ (|t| *D+|δ|)*(1+N) := by
  have h := restrictedCanonicalHaarLog_bound S hS C hC k e a₀ hk lam v u t cap δ hcap (A p.1.1) (p.1.2,p.2)
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left (hA p.1.1) (abs_nonneg t)) (le_refl |δ|)) (by positivity)

end InvariantIsing

end

end OAI
