import OAI.Probability.FreeIsing.Energy.ProgressiveIsingCovariance
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitiveFubini
import OAI.Probability.FreeIsing.Martingales.ArtanhMartingaleFormula

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367.ArtanhResponseCoefficients
open ArtanhMartingaleFormula

theorem firstWeight_mul (m c : ℝ) :
    firstWeight m * c = c / (1 - m ^ 2) := by
  simp only [firstWeight, div_eq_mul_inv, one_mul, mul_comm]

theorem secondWeight_mul_tsum_sq {ι : Type*} (m : ℝ) (C : ι → ℝ) :
    secondWeight m * (∑' i, C i ^ 2) =
      m * (∑' i, (C i / (1 - m ^ 2)) ^ 2) := by
  rw [show (∑' i, (C i / (1 - m ^ 2)) ^ 2) =
      (∑' i, C i ^ 2) / (1 - m ^ 2) ^ 2 by
    simp only [div_pow, tsum_div_const]]
  simp only [secondWeight, div_eq_mul_inv]
  ring

theorem firstWeight_infiniteGibbsCovariance {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (y : TreeVertex d → ℝ) :
    firstWeight (infiniteGibbsSpinMean beta v y) * infiniteGibbsCovariance beta v w y =
      infiniteGibbsResponse beta v w y := firstWeight_mul _ _

theorem secondWeight_infiniteGibbsCovarianceRow {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (y : TreeVertex d → ℝ) :
    secondWeight (infiniteGibbsSpinMean beta v y) *
      (∑' w, infiniteGibbsCovariance beta v w y ^ 2) =
      infiniteGibbsSpinMean beta v y * infiniteGibbsResponseRow beta v y :=
  secondWeight_mul_tsum_sq _ _

theorem isStronglyProgressive_covarianceSquareRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F (fun t ω =>
      ∑' w, infiniteGibbsCovariance beta v w (fun i => X i t ω) ^ 2) := by
  intro T
  have hc (w : TreeVertex d) :=
    isStronglyProgressive_infiniteGibbsCovariance F beta v w X hX T
  let : MeasurableSpace Ω := F T
  exact StronglyMeasurable.tsum (fun w => (hc w).pow 2)

theorem ae_all_primitive_eq_responseDrift
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {F : Filtration ℝ≥0 mΩ} (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i))
    {M : ℝ≥0 → Ω → ℝ} (hM : IsStronglyProgressive F M)
    (hversion : ∀ t, M t =ᵐ[μ]
      fun ω => infiniteGibbsSpinMean beta v (fun i => X i t ω)) :
    ∀ᵐ ω ∂μ, ∀ t,
      nnrealTimePrimitive (fun s p => secondWeight (M s p) *
        (∑' w, infiniteGibbsCovariance beta v w (fun i => X i s p) ^ 2)) t ω =
      nnrealTimePrimitive (fun s p => M s p *
        infiniteGibbsResponseRow beta v (fun i => X i s p)) t ω := by
  have hleft : IsStronglyProgressive F (fun s p => secondWeight (M s p) *
      (∑' w, infiniteGibbsCovariance beta v w (fun i => X i s p) ^ 2)) := by
    intro T
    exact (stronglyMeasurable_secondWeight (hM T)).mul
      (isStronglyProgressive_covarianceSquareRow F beta v X hX T)
  have hright := hM.mul (isStronglyProgressive_infiniteGibbsResponseRow F beta v X hX)
  apply ae_all_nnrealTimePrimitive_eq_of_modification hleft hright
  intro t
  filter_upwards [hversion t] with ω hω
  rw [hω]
  exact secondWeight_infiniteGibbsCovarianceRow beta v _

end Problem367.ArtanhResponseCoefficients

end

end OAI
