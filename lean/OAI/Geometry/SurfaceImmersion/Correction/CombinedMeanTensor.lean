import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanGeometry
import OAI.Geometry.SurfaceImmersion.Correction.CombinedRootMean
import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! The three actual components of the combined zero-phase mean, with one
finite loss and scale-independent square-root trial estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes
open PhaseMean (firstDirection secondDirection firstDirection_norm secondDirection_norm)
variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}
variable {F : RField 4} {V : Set SmallModes.Base}

def combinedMeanTensor (P : Fin 3 → Fin n → Expression) (δ τ ε : ℝ) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (x : Base) : Fin 3 → ℝ :=
  fun i => combinedSeedMean (P i) δ τ ε G hF h K hKV R q b (firstDirection i) (secondDirection i) x

theorem combinedRootTensor_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V) {L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) {r R₀ C P₀ N : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP₀ : 0 ≤ P₀) (hN : 0 ≤ N) :
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
      ∀ (ψ : SupportedField (F := ℝ) (modeSupport K))
        (u v : SmallModes.Base → ℝ) (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V)
        (hru : Set.MapsTo u V (Set.Icc r R₀)) (hrv : Set.MapsTo v V (Set.Icc r R₀))
        (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) ψ ≤ P₀ →
      WeightedBound V s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) C u →
      WeightedBound V s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) C v →
      WeightedBound V s (m + tensorOrder P + 1 + (q + 1) * (L + 1)) d (fun x => u x - v x) →
      let b := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ u hu (fun _ hx => hr.trans_le (hru hx).1)
      let c := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ v hv (fun _ hx => hr.trans_le (hrv hx).1)
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * E)
        (combinedMeanTensor P δ τ ε G hF h K hKV R q b) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * (2 * E) * d)
        (fun x => combinedMeanTensor P δ τ ε G hF h K hKV R q b x -
          combinedMeanTensor P δ τ ε G hF h K hKV R q c x) := by
  classical
  have hex (i : Fin 3) := combinedRootMean_bounds (L := L) hU hO hQ hQO (P i) (hP i) m B₀ hB₀
    hF h K hKU hKV B D hB hD q (R₀ := R₀) hr hC hP₀ hN
  choose E hE he using hex
  refine ⟨∑ i, E i, Finset.sum_nonneg (fun i _ => hE i), ?_⟩
  intro G hG s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hc R hR hbN
    ψ u v hu hv hru hrv d hd hψ hbu hbv hdu
  let b := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ u hu (fun _ hx => hr.trans_le (hru hx).1)
  let c := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ v hv (fun _ hx => hr.trans_le (hrv hx).1)
  have ho (i : Fin 3) : order (P i) ≤ tensorOrder P :=
    Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ i)
  have hl (i : Fin 3) : loss (P i) ≤ tensorLoss P :=
    Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ i)
  have hi (i : Fin 3) : m + order (P i) + 1 + (q + 1) * (L + 1) ≤
      m + tensorOrder P + 1 + (q + 1) * (L + 1) := by have := ho i; omega
  have hb (i : Fin 3) := he i G hG s δ τ ε p hδ hτ hs hτs hs1 hε hε1 ((hl i).trans hp)
    hsmall hGQ (hGb.mono_order (Nat.add_le_add_left (ho i) m)) hc R hR
    (hbN.mono_order (hi i)) ψ u v hu hv hru hrv d hd
    ((supportedWeightedSeminorm_mono s (hi i) ψ).trans hψ)
    (hbu.mono_order (hi i)) (hbv.mono_order (hi i)) (hdu.mono_order (hi i))
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
  dsimp only
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
