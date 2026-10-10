import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanTensor

namespace OAI

/-! Common-order estimates for the combined tensor mean on bounded supported
amplitudes, ready for substitution of the actual trial-field amplitudes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes
open PhaseMean (firstDirection secondDirection firstDirection_norm secondDirection_norm)
variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}
variable {F : RField 4} {V : Set SmallModes.Base}

theorem combinedSeedTensor_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V) {L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G)
      (s : ℝ≥0) (δ τ ε : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      tensorLoss P ≤ p → τ / s + ε / τ ^ p ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B₀ (lowJet G) →
      (∀ m, SmallModes.ReconstructionCoefficientBound (fun x => complexify (F x)) V s (m + 1) (B m)) →
      ∀ (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) s m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) s (m + L) Z) →
      WeightedBound V s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) N (freeNormal F) →
      ∀ (b c : SupportedField (F := ℝ) (modeSupport K)) (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) b ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) c ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) (b - c) ≤ A * d →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * E)
        (combinedMeanTensor P δ τ ε G hF h K hKV R q b) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * (2 * E) * d)
        (fun x => combinedMeanTensor P δ τ ε G hF h K hKV R q b x -
          combinedMeanTensor P δ τ ε G hF h K hKV R q c x) := by
  classical
  have hex (i : Fin 3) := combinedSeedMean_bounds (L := L) hU hO hQ hQO (P i) (hP i) m B₀ hB₀
    hF h K hKU hKV B D hB hD q A N hA hN
  choose E hE he using hex
  refine ⟨∑ i, E i, Finset.sum_nonneg (fun i _ => hE i), ?_⟩
  intro G hG s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hc R hR hbN b c d hd hbb hcc hbc
  have ho (i : Fin 3) : order (P i) ≤ tensorOrder P :=
    Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ i)
  have hl (i : Fin 3) : loss (P i) ≤ tensorLoss P :=
    Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ i)
  have hi (i : Fin 3) : m + order (P i) + 1 + (q + 1) * (L + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (L + 1) := by have := ho i; omega
  have hb (i : Fin 3) := he i G hG s δ τ ε p hδ hτ hs hτs hs1 hε hε1 ((hl i).trans hp)
    hsmall hGQ (hGb.mono_order (Nat.add_le_add_left (ho i) m)) hc R hR
    (hbN.mono_order (hi i)) b c d hd
    ((supportedWeightedSeminorm_mono s (hi i) b).trans hbb)
    ((supportedWeightedSeminorm_mono s (hi i) c).trans hcc)
    ((supportedWeightedSeminorm_mono s (hi i) (b - c)).trans hbc)
    (firstDirection i) (secondDirection i) (firstDirection_norm i) (secondDirection_norm i)
  have hEsum : 0 ≤ ∑ i, E i := Finset.sum_nonneg (fun i _ => hE i)
  have hsum (i : Fin 3) : E i ≤ ∑ j, E j :=
    Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hsm (a : SupportedField (F := ℝ) (modeSupport K)) (i : Fin 3) :
      ContDiff ℝ ∞ (combinedSeedMean (P i) δ τ ε G hF h K hKV R q a (firstDirection i) (secondDirection i)) :=
    combinedSeedMean_smooth hU hO (hP i) δ τ ε hG (fun _ hx => hQO (hGQ hx))
      hF h K hKU hKV R q a (firstDirection i) (secondDirection i)
  constructor
  · apply WeightedBound.pi isOpen_univ.uniqueDiffOn hs (by positivity)
    · intro i
      exact (hsm b i).contDiffOn
    · intro i
      exact (hb i).1.mono_const (mul_le_mul_of_nonneg_left (hsum i) hη)
  · apply WeightedBound.pi isOpen_univ.uniqueDiffOn hs (by positivity)
    · intro i
      exact ((hsm b i).sub (hsm c i)).contDiffOn
    · intro i
      apply (hb i).2.mono_const
      gcongr
      exact hsum i

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
