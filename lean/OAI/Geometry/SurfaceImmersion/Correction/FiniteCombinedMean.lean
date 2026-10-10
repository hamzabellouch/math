import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanMajorants

namespace OAI

/-! Finite adjustment by the actual combined metric and polynomial mean.
The threshold is chosen before the short scale and perturbation operator. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates FiniteMean
open JetPolynomial (SupportedField supportedWeightedSeminorm)
open JetPolynomial.Perturbation (modeSupport)

variable {n : ℕ} {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

theorem finite_combined_mean_adjustment (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    (hKV : (modeSupport K : Set Base) ⊆ V)
    {S : Set Base} (hS : IsClosed S) (hSU : S ⊆ U)
    (hsp : ∀ x ∈ U, χ x ∈ (modeSupport K : Set Base) → x ∈ S)
    {P : Fin 3 → Fin n → JetPolynomial.Expression} {J : Set JetPolynomial.Base}
    {O Q₀ : Set JetPolynomial.LowJet} (hJ : IsOpen J) (hO : IsOpen O)
    (hQ₀ : IsCompact Q₀) (hQO : Q₀ ⊆ O) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (hKJ : (K : Set JetPolynomial.Base) ⊆ J)
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGQ : Set.MapsTo (JetPolynomial.lowJet G) J Q₀)
    {L : ℕ} (D B₀ : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) (hB₀ : ∀ m, 1 ≤ B₀ m)
    (hGb : ∀ m, WeightedBound J s (m + JetPolynomial.Perturbation.tensorOrder P) (B₀ m) (JetPolynomial.lowJet G))
    (q steps : ℕ) {H : Base → Tensor} {r₀ : ℝ} (hgap : r₀ < r)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H) :
    let ℓ := JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (δ τ ε : ℝ) (p : ℕ), 0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      JetPolynomial.Perturbation.tensorLoss P ≤ p → τ / s + ε / τ ^ p ≤ η₀ →
      ∀ (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ (m + L) Z) →
      let T := extendedCombinedMean h hρ hKV P G δ τ ε R q
      ∀ j ≤ steps, ContDiff ℝ ∞ (fixedTrial H T j) ∧
        InTrialBall Set.univ reference r (fixedTrial H T j) ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound ℓ C β j m) (fixedTrial H T j)) ∧
        (∀ m, WeightedBound Set.univ s m
          (differenceBound ℓ C β κ j m * (τ / s + ε / τ ^ p) ^ (j + 1))
          (fixedTrial H T j + T (fixedTrial H T j) - H)) := by
  obtain ⟨β, κ, hm⟩ := extendedCombinedMean_majorants (L := L) h d hs hs1 hρ hKV hS hSU hsp
    hJ hO hQ₀ hQO hP hKJ hG hGQ D B₀ hD hB₀ hGb q
  obtain ⟨η₀, hη₀, hη₁, ht⟩ := finite_substitution_uniform (B := β) (K := κ)
    isOpen_univ.uniqueDiffOn hs.le hgap hC hH.contDiffOn (fun x _ => hH0 x) hbH steps
  refine ⟨β, κ, η₀, hη₀, hη₁, ?_⟩
  intro δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR
  have hη : 0 < τ / s + ε / τ ^ p :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  have hT := hm δ τ ε p hδ hτ hτs hε hε1 hp (hsmall.trans hη₁) R hR
  dsimp only
  intro j hj
  obtain ⟨ha, hb, hc, hd⟩ := ht _ hT _ hη hsmall j hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (by simpa only [trial_rescaledMean hη.ne'] using ha)
  · simpa only [trial_rescaledMean hη.ne'] using hb
  · simpa only [trial_rescaledMean hη.ne'] using hc
  · simpa only [trial_rescaledMean hη.ne', rescaledMean_self hη.ne'] using hd

end ClosedSurfaceR4.PhaseMean

end

end OAI
