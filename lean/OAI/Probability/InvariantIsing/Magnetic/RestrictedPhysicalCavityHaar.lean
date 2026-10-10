import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorCutoffLaw
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorJointHaar

namespace OAI

/-! Joint Haar factorization for the normalized cavity observable.
Compression-dependent coefficients and the selected frame are retained
inside the same normalized two-replica test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_physical_cavity_haar {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
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
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : (Fin m → Matrix (Fin n) (Fin n) ℝ) → CavityFactorBlocks d n)
    (hA : Measurable A)
    (F : ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d) →
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : Measurable (Function.uncurry F))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p σ, |F p σ| ≤ C) :
    (∫ U, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A (cavityCompressionGrams g U))
      (F (cavityCompressionGrams g U,
        cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U))
      (cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ U, ∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A (cavityCompressionGrams g U))
      (F (cavityCompressionGrams g U,
        cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)))
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ := by
  let Ω := (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d
  let a : Ω → CavityFactorBlocks d n := fun p => A p.1
  let p : Ω → CavityProjectorFrame N m d := Prod.snd
  have ha : Measurable a := hA.comp measurable_fst
  have hp : Measurable p := measurable_snd
  have hm := measurable_restrictedProjectorCavityMean (Ω := Ω)
    (N := N) (n := n) (m := m) (d := d) (depth := depth) S hS Cset hCset T c u t D a ha p hp F hF
  have hbnd : ∀ q : Ω, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D (a q) (F q) (p q)‖ ≤ C := by
    intro q
    exact restrictedProjectorCavityMean_bound (N := N) (n := n) (m := m) (d := d)
      (depth := depth) S hS Cset hCset T c u t D (a q) (F q) hC (hb q) (p q)
  exact cavity_labeled_projector_joint_haar g k ek e es B₀ a₀ l w hg hln hw μ ν
    (fun q : Ω => restrictedProjectorCavityMean S hS Cset hCset T c u t D (a q) (F q) (p q)) hm C hbnd

end InvariantIsing

end

end OAI
