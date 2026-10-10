import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorCoefficientError
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorHaarMean

namespace OAI

/-! The normalized coefficient replacement for the actual independent
compression and base-Haar factors. The chosen spectral axes remain in
the same base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

lemma measurable_restrictedProjectorHaarMean {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (a₀ : Fin d → Fin m)
    (ν : Measure (Orthogonal N)) [SFinite ν] (T : LabeledTree depth) (c : Fin m → ℝ)
    (u : ℕ → ℝ) (t D : ℝ) (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    Measurable (fun ω => ∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D (A ω) F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) := by
  let a : Ω × Orthogonal N → CavityFactorBlocks d n := fun p => A p.1
  let p : Ω × Orthogonal N → CavityProjectorFrame N m d := fun q =>
    cavityLabeledProjectorAction q.2 (cavityCanonicalProjectorFrame k e a₀)
  have ha : Measurable a := hA.comp measurable_fst
  have hp : Measurable p := (measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd
  have hF : Measurable (fun q : (Ω × Orthogonal N) ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F q.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hm := measurable_restrictedProjectorCavityMean (N := N) (n := n) (m := m)
    (d := d) (depth := depth) S hS Cset hCset T c u t D a ha p hp (fun _ => F) hF
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma restrictedProjectorHaarMean_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (a₀ : Fin d → Fin m)
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |∫ V, restrictedProjectorCavityMean S hS Cset hCset T c u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤ M := by
  have hb : ∀ᵐ V ∂ν, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀))‖ ≤ M :=
    ae_of_all _ fun V => restrictedProjectorCavityMean_bound S hS Cset hCset T c u t D A F hM hF _
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma restricted_projector_haar_coefficient_error {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (lam v : Fin m → ℝ)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A A' : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M s : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
    |(∫ V, restrictedProjectorCavityMean S hS Cset hCset T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) -
      ∫ V, restrictedProjectorCavityMean S hS Cset hCset T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A' F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤
      4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2 := by
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let p := fun V : Orthogonal N =>
    cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
  let g : Fin N → Fin m := fun i => Sum.elim (fun w => w.1) a₀ (e.symm i)
  have hpV (V : Orthogonal N) : (p V).1 =
      fun a => cavitySpectralProjector V (cavitySpectralGroup g a) :=
    cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hp : Measurable p := measurable_cavityCanonicalProjectorAction k e a₀
  have hFs : Measurable (fun q : Orthogonal N ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F q.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hi (B : CavityFactorBlocks d n) :
      Integrable (fun V => restrictedProjectorCavityMean S hS Cset hCset T c u t D B F (p V)) ν :=
    Integrable.of_bound
      (measurable_restrictedProjectorCavityMean S hS Cset hCset T c u t D (fun _ => B) measurable_const
        p hp (fun _ => F) hFs).aestronglyMeasurable M
      (ae_of_all _ fun V => restrictedProjectorCavityMean_bound S hS Cset hCset T c u t D B F hM hF (p V))
  rw [← integral_sub (hi A) (hi A')]
  have hb : ∀ᵐ V ∂ν, ‖restrictedProjectorCavityMean S hS Cset hCset T c u t D A F (p V) -
      restrictedProjectorCavityMean S hS Cset hCset T c u t D A' F (p V)‖ ≤
      4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2 := by
    apply ae_of_all
    intro V
    have hh := restricted_projector_coefficient_error
      (N := N) (n := n) (m := m) (d := d) (depth := depth)
      S hS Cset hCset g V T lam v u hu t hD A A' (p V) (hpV V) F hM hF hs
    rw [Real.norm_eq_abs]
    convert hh using 1
    ring
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end InvariantIsing

end

end OAI
