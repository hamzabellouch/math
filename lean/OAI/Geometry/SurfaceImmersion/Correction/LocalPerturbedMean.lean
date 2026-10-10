import OAI.Geometry.SurfaceImmersion.Correction.UniformPerturbedMean

namespace OAI

/-! The actual mean only needs to reconstruct on the local correction
domain. Outside that domain the compactly supported cutoff can vanish. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

lemma charted_quadratic_mean_residual_on {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hρ : 0 < ρ) {δ : ℝ}
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) {A H : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H)
    (hdecomp : ∀ x ∈ V, chartedFamilyLeading d hρ A x = A x) {m : ℕ} {C : ℝ}
    (hb : WeightedBound Set.univ s m C (A+chartedFamilyMean d hρ δ q A-H)) :
    WeightedBound V s m (δ^2*C)
      (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0-δ^2 • H) := by
  have hh := (hb.restrict_open hV).const_smul hV.uniqueDiffOn
    ((hA.add (chartedFamilyMean_smooth d hρ δ q A)).sub hH).contDiffOn (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  apply hh.congr
  intro x hx
  rw [charted_family_zero_phase_identity d hρ hδ hτ q A]
  simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,hdecomp x hx,smul_sub]

theorem uniform_perturbed_mean_on {V : Set SmallModes.Base} (hV : IsOpen V) {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (p : ι → ChartedMeanProfile P)
    {ρ R r r₀ : ℝ} (hρ : 0 < ρ) (hgap : r₀ < r) (q steps : ℕ)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (reference H : SmallModes.Base → Tensor), ContDiff ℝ ∞ H →
      (∀ x, ‖H x - reference x‖ ≤ r₀) →
      (∀ m, WeightedBound Set.univ s m (C m) H) →
      ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {ε τ : ℝ}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ tensorLoss P ≤ η₀ →
      (∀ A, ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
        ∀ x ∈ V, chartedFamilyLeading d hρ A x = A x) →
      ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps, ∃ A : SmallModes.Base → Tensor,
        ContDiff ℝ ∞ A ∧ InTrialBall Set.univ reference r A ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound L C β j m) A) ∧
        (∀ m, WeightedBound V s m
          (δ ^ 2 * (differenceBound L C β κ j m *
            (τ / s + ε / τ ^ tensorLoss P) ^ (j + 1)))
          (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 -
            δ ^ 2 • H)) := by
  obtain ⟨β,κ,hm⟩ := uniform_charted_family_majorants (R := R) p hρ q
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := finite_substitution_uniform_inputs
    (E := SmallModes.Base) (F := Tensor) (B := β) (K := κ) hgap hC steps
  refine ⟨β,κ,η₀,hη₀,hη₁,?_⟩
  intro s hs hs1 reference H hH hH0 hbH G hG φ K ε τ c d hd
    hτ hτs hε hε1 hsmall hdecomp δ hδ j hj
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨ha,hb,hc,he⟩ := ht Set.univ isOpen_univ.uniqueDiffOn s s.coe_nonneg
    reference H hH.contDiffOn (fun x _ => hH0 x) hbH _
    (hm d hd hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁) δ hδ) _ hη hsmall j hj
  have ha' : ContDiff ℝ ∞ (fixedTrial H (chartedFamilyMean d hρ δ q) j) :=
    contDiffOn_univ.mp (by simpa only [trial_rescaledMean hη.ne'] using ha)
  have hb' : InTrialBall Set.univ reference r (fixedTrial H (chartedFamilyMean d hρ δ q) j) := by
    simpa only [trial_rescaledMean hη.ne'] using hb
  refine ⟨fixedTrial H (chartedFamilyMean d hρ δ q) j,ha',hb',?_,?_⟩
  · simpa only [trial_rescaledMean hη.ne'] using hc
  · intro m
    apply charted_quadratic_mean_residual_on d hV hρ hδ.ne' hτ.ne' q ha' hH (hdecomp _ ha' hb')
    simpa only [trial_rescaledMean hη.ne',rescaledMean_self hη.ne'] using he m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
