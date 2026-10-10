import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain
import OAI.Probability.InvariantIsing.Spectral.SpectralPathLimit
import OAI.Probability.IsingPerceptron.ContactFaces

namespace OAI

/-! Lower finite-grid trials approximate each monotone overlap path in L1,
remain below one, and do not increase the entropy functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def lowerGridPath (p : OverlapPath) (n : ℕ) : OverlapPath where
  val := lowerGrid p.val n
  monotone := lowerGrid_monotone p.monotone n
  nonneg s := (lowerGrid_mem (fun u => ⟨p.nonneg u, p.le_one u⟩) n s).1
  le_one s := (lowerGrid_mem (fun u => ⟨p.nonneg u, p.le_one u⟩) n s).2

lemma lowerGridPath_below_one (p : OverlapPath) (n : ℕ) (s : ℝ) :
    lowerGridPath p n s ≤ 1 - 1 / (n + 1 : ℕ) := by
  change (1 - 1 / (n + 1 : ℕ) : ℝ) * _ ≤ _
  exact mul_le_of_le_one_right (lowerGrid_factor_nonneg n) (p.le_one _)

lemma lowerGridPath_le (p : OverlapPath) (n : ℕ) :
    (lowerGridPath p n).val ≤ᵐ[pathMeasure] p.val := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact lowerGrid_le p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩) n hs.1.le

lemma lowerGridPath_entropy_le (p : OverlapPath) (n : ℕ) :
    entropyFunctional (lowerGridPath p n) ≤ entropyFunctional p :=
  entropyFunctional_mono (lowerGridPath_le p n)

lemma lowerGridPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1))
    (s : ℝ) (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    lowerGridPath p n s = (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)) := by
  change lowerGrid p.val n s = _
  simp only [lowerGrid, floor_on_uniformCell n i hs]

lemma lowerGridPath_L1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have hi := lowerGrid_integral_tendsto p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩)
  change Tendsto (fun n => ∫ s, lowerGridPath p n s ∂pathMeasure) atTop
    (𝓝 (∫ s, p s ∂pathMeasure)) at hi
  have he (n : ℕ) : (∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) =
      (∫ s, p s ∂pathMeasure) - ∫ s, lowerGridPath p n s ∂pathMeasure := by
    rw [← integral_sub p.integrable (lowerGridPath p n).integrable]
    apply integral_congr_ae
    filter_upwards [lowerGridPath_le p n] with s hs
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    ring
  simpa only [he, sub_self] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ s, p s ∂pathMeasure)
      atTop (𝓝 (∫ s, p s ∂pathMeasure))).sub hi)

lemma lowerGridPath_spectral_tendsto {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Tendsto (fun n => spectralFunctional (finiteR ρ eig hρ hρsum) (lowerGridPath p n))
      atTop (𝓝 (spectralFunctional (finiteR ρ eig hρ hρsum) p)) := by
  have ht := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hρsum p
    (lowerGridPath p) (lowerGridPath_L1_tendsto p) zero_le_one
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ zero_le_one, one_mul] using ht

end InvariantIsing

end

end OAI
