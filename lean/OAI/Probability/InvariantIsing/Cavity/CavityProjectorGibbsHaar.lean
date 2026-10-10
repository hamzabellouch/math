import OAI.Probability.InvariantIsing.Cavity.CavityProjectorMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorJointHaar
import OAI.Probability.InvariantIsing.Cavity.CavityBaseOverlap

namespace OAI

/-! Joint averaging of the actual projector-based Gibbs law and its
compression-dependent bounded replica tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityProjectorReplicaMean_joint {N n m d depth r : ℕ}
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ)
    (F : ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d) →
      (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d =>
      cavityProjectorReplicaMean T c u (fun s => F (p.1,s)) p.2) := by
  have hH := measurable_cavityProjectorHamiltonian_pullback
    (fun p : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d => p.2.1)
    measurable_snd.fst c u (depth := depth)
  exact (measurable_referenceReplicaMean _ hH
    (hF.comp (measurable_fst.fst.prodMk measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

theorem cavity_physical_gibbs_projector_haar {N n m d depth r : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < w a)
    (hln : ∀ a, l a+n ≤ w a) (hw : ∀ a, w a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ)
    (F : ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d) →
      (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ p σ, |F p σ| ≤ C) :
    (∫ U, cavityProjectorReplicaMean T c u
      (fun p => F (cavityCompressionGrams g U,p))
      (cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ U, ∫ V, cavityProjectorReplicaMean T c u
      (fun p => F (cavityCompressionGrams g U,p))
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ := by
  exact cavity_labeled_projector_joint_haar g k ek e es B₀ a₀ l w hg hln hw μ ν
    (fun p => cavityProjectorReplicaMean T c u (fun s => F (p.1,s)) p.2)
    (measurable_cavityProjectorReplicaMean_joint T c u F hF) C
    (fun p => cavityProjectorReplicaMean_bound T c u (fun s => F (p.1,s)) hC
      (fun s σ => hb (p.1,s) σ) p.2)

lemma cavityCanonicalProjectorFrame_action_fst {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) :
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).1 =
      fun a => cavitySpectralProjector V
        (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) := by
  funext a
  have hd : (fun j : Fin N => Sum.elim (fun w => if w.1=a then (1:ℝ) else 0)
      (fun j => if a₀ j=a then 1 else 0) (e.symm j)) =
      (fun j => if j ∈ cavitySpectralGroup
        (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a then 1 else 0) := by
    funext j
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h : e.symm j with w | j₀ <;> rfl
  exact congrArg (fun f : Fin N → ℝ => cavityConjugate V (Matrix.diagonal f)) hd

 theorem cavity_canonical_projector_replica {N m d depth r : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (F : CavityProjectorFrame N m d → (Fin r → Spin N × LabeledLeaf depth) → ℝ) :
    let p := cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    cavityProjectorReplicaMean (N := N) (m := m) (d := d) (depth := depth) (r := r)
      T (fun a => t*lam a+2*perturbationScale N*v a) u F p =
      ∫ z, referenceReplicaMean ν
        (cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues
            (fun j => lam (Sum.elim (fun w => w.1) a₀ (e.symm j)))
            (cavityBaseGroup k e a₀) v t) (cavityBaseGroup k e a₀) u z)
        (F p) ∂gaussianCoordinates := by
  intro p ν
  unfold cavityProjectorReplicaMean
  have hp : p.1 = fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) :=
    cavityCanonicalProjectorFrame_action_fst k e a₀ V
  rw [hp]
  have h := cavity_projector_gibbs_replica (N := N) (m := m) (depth := depth) (r := r)
    (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) V T lam v u t (F p)
  have hI : cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) =
      cavityBaseGroup k e a₀ := rfl
  rw [hI] at h
  exact h

end InvariantIsing

end

end OAI
