import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.MasterPotentialEvent
import OAI.Analysis.CoulombIonization.RadialBounds.RadialCenterRawComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma normalized_event_integral {N K : ℕ} (μ ν : Measure (Configuration N))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    {p : ℝ} (hp : 0 < p)
    (hlaw : ν = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {f : Configuration N → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂ν) = p⁻¹*(∫ z in A, f z.1 ∂physicalObservationLaw μ K) := by
  rw [hlaw,integral_smul_measure,integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hp.le,smul_eq_mul]

theorem normalized_master_event_loss {N K : ℕ} (μ ν : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : ν = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A)) :
    0 ≤ (∫ x, rawPotential y x ∂ν)-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ∧
    (∫ x, rawPotential y x ∂ν)-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ≤
      ∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂ν := by
  have hh := master_potential_event_loss μ ell j y hi he hc hcL hr hs hs1 hg hcg hgn hrad hgs hA
  rw [normalized_event_integral μ ν A hp hlaw (rawPotential_measurable y),
    normalized_event_integral μ ν A hp hlaw (rawLocalPotential_measurable N y _),←mul_sub]
  exact ⟨mul_nonneg (inv_nonneg.mpr hp.le) hh.1,
    mul_le_mul_of_nonneg_left hh.2 (inv_nonneg.mpr hp.le)⟩

def expectedRadialPatchCenter {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  ∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
    weightedPatchCenter (orderedCutForm p hp ψ c) k Z lam y (t-4*b) u

def radialPotentialError {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam q : ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
    (∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (χ c) k Z lam y (t-4*b) hb (radialPatchRetention N y t b c k) u))+
  (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
  (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ+
  (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
  Real.sqrt (formMass ψ)*Real.sqrt
    (∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
      (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) k u))/(t-7*b)

theorem original_master_radial_center_comparison {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : formRawLaw ψ = (ENNReal.ofReal p)⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 7*b < t) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    |(Z/‖y‖-lam)*formMass ψ-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K)-expectedRadialPatchCenter ψ y ht hb Z lam| ≤
      radialPotentialError ψ y ht hb Z lam q+
      (∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂formRawLaw ψ) := by
  have hraw := radial_center_field_quantitative hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR
  change |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
    expectedRadialPatchCenter ψ y ht hb Z lam| ≤ radialPotentialError ψ y ht hb Z lam q at hraw
  have hm := normalized_master_event_loss μ (formRawLaw ψ) ell j y hi he hc hcL hr hs hs1
    hg hcg hgn hrad hgs hA hp hlaw
  have hid (a b c d : ℝ) : a-b-c = (a-d-c)+(d-b) := by ring
  rw [hid _ _ _ (∫ x, rawPotential y x ∂formRawLaw ψ)]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg hm.1]
  exact add_le_add hraw hm.2

end CoulombAtom

end

end OAI
