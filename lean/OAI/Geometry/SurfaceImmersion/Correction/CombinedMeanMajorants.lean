import OAI.Geometry.SurfaceImmersion.Correction.ExtendedCombinedMean
import OAI.Geometry.SurfaceImmersion.Correction.FixedMeanSubstitution

namespace OAI

/-! Scale-independent majorants for the actual extended combined mean. -/
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

theorem extendedCombinedMean_majorants (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
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
    (q : ℕ) :
    ∃ β κ : ℕ → ℝ → ℝ, ∀ (δ τ ε : ℝ) (p : ℕ),
      0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      JetPolynomial.Perturbation.tensorLoss P ≤ p → τ / s + ε / τ ^ p ≤ 1 →
      ∀ (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ (m + L) Z) →
      MeanBounds Set.univ s reference r (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1))
        (rescaledMean (τ / s + ε / τ ^ p) (extendedCombinedMean h hρ hKV P G δ τ ε R q)) β κ := by
  have hex (m : ℕ) (C : ℝ) := localCombinedMean_estimates (L := L) h d hs hs1 hρ hKV
    hJ hO hQ₀ hQO hP hKJ hG hGQ D hD q m C (B₀ m) (hB₀ m) (hGb m)
  choose β κ hβ hκ he using hex
  refine ⟨β, κ, ?_⟩
  intro δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR
  have hη : 0 < τ / s + ε / τ ^ p :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  have hsm (A : Base → Tensor) := extendedCombinedMean_smooth h hρ hKV hS hSU hsp hJ hO hP hG
    (fun _ hx => hQO (hGQ hx)) hKJ δ τ ε R q A
  have hball {A : Base → Tensor} (ha : InTrialBall Set.univ reference r A) :
      InTrialBall U reference r A := fun x _ => ha x (Set.mem_univ x)
  apply rescaledMean_bounds isOpen_univ.uniqueDiffOn hη _ β κ
    (fun m C _ => hβ m C) (fun m C _ => hκ m C)
  · intro A _ _
    exact (hsm A).contDiffOn
  · intro m C A hC hA hAball hbA
    have hz : WeightedBound U s (m + (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1))) 0
        (A - A) := by
      apply (weightedBound_zero U s _ (F := Tensor)).congr
      intro x _
      exact sub_self (A x)
    have hh := (he m C δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR A A 0 (zero_le_one.trans hC)
      le_rfl (hA.mono (Set.subset_univ U)) (hA.mono (Set.subset_univ U)) (hball hAball) (hball hAball)
      (hbA.restrict_open h.openU) (hbA.restrict_open h.openU) hz).1
    exact extendedCombinedMean_value h hρ hKV hS hSU hsp P G δ τ ε R q A
      (mul_nonneg hη.le (zero_le_one.trans (hβ m C))) hh
  · intro m C a A B hC ha hA hB hAball hBball hbA hbB hab
    have hh := (he m C δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR A B a (zero_le_one.trans hC)
      ha (hA.mono (Set.subset_univ U)) (hB.mono (Set.subset_univ U)) (hball hAball) (hball hBball)
      (hbA.restrict_open h.openU) (hbB.restrict_open h.openU) (hab.restrict_open h.openU)).2
    exact extendedCombinedMean_difference h hρ hKV hS hSU hsp P G δ τ ε R q A B
      (mul_nonneg (mul_nonneg (zero_le_one.trans (hκ m C)) hη.le) ha) hh

end ClosedSurfaceR4.PhaseMean

end

end OAI
