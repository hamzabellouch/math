import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoherentBessel
import OAI.Analysis.CoulombIonization.Variational.CoherentDensity

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

lemma nonneg_series_eq_of_integral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ} {d : α → ℝ}
    (hf : ∀ i, Integrable (f i) μ) (hn : ∀ i x, 0 ≤ f i x) (hd : Integrable d μ)
    (hle : ∀ s : Finset ι, ∀ x, (∑ i ∈ s, f i x) ≤ d x)
    (htrace : HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, d x ∂μ)) :
    (fun x => ∑' i, f i x) =ᵐ[μ] d := by
  have hs (x) : Summable (fun i => f i x) := summable_of_sum_le (fun i => hn i x) (fun s => hle s x)
  have hb (x) : (∑' i, f i x) ≤ d x := (hs x).tsum_le_of_sum_le (fun s => hle s x)
  have hi : Integrable (fun x => ∑' i, f i x) μ :=
    hd.mono' (AEStronglyMeasurable.tsum (fun i => (hf i).aestronglyMeasurable))
      (Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (tsum_nonneg (fun i => hn i x))]; exact hb x))
  have hh := hasSum_integral_of_dominated_convergence (fun i x => f i x)
    (fun i => (hf i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun x => (Real.norm_of_nonneg (hn i x)).le))
    (Eventually.of_forall hs) hi (Eventually.of_forall (fun x => (hs x).hasSum))
  exact (integral_eq_iff_of_ae_le hi hd (Eventually.of_forall hb)).1 (hh.unique htrace)

lemma coherentOrbital_density_tsum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    (fun x : Space => ∑' i : CoherentPositiveIndex hg.continuous hcg μ,
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
      =ᵐ[volume] coherentDensity g μ := by
  apply nonneg_series_eq_of_integral volume
  · intro i
    exact ((coherentOrbital_memLp hg hcg μ hK hμ i.1).norm.integrable_sq).const_mul _
  · intro i x
    exact mul_nonneg i.2.le (sq_nonneg _)
  · exact coherentDensity_integrable hg.continuous hcg μ hK hμ
  · exact fun s x => coherentOrbital_density_le hg.continuous hcg μ hK hμ s x
  · simp only [integral_const_mul,coherentOrbital_mass hg hcg μ hK hμ,mul_one,
      coherentDensity_mass hg.continuous hcg μ hK hμ]
    exact coherentPositiveWeight_hasSum hg.continuous hcg μ

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

lemma nonneg_series_weight_hasSum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ} {d W : α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hn : ∀ i x, 0 ≤ f i x)
    (hw : AEStronglyMeasurable W μ) (hwd : Integrable (fun x => |W x| *d x) μ)
    (htrace : ∀ᵐ x ∂μ, HasSum (fun i => f i x) (d x)) :
    HasSum (fun i => ∫ x, W x*f i x ∂μ) (∫ x, W x*d x ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun i x => |W x| *f i x)
    (fun i => hw.mul (hf i))
  · intro i
    filter_upwards [] with x
    rw [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn i x)]
  · filter_upwards [htrace] with x hx
    exact (hx.mul_left |W x|).summable
  · apply hwd.congr
    filter_upwards [htrace] with x hx
    exact (hx.mul_left |W x|).tsum_eq.symm
  · filter_upwards [htrace] with x hx
    exact hx.mul_left (W x)

lemma coherentOrbital_density_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    ∀ᵐ x : Space ∂volume, HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
        (coherentDensity g μ x) := by
  filter_upwards [coherentOrbital_density_tsum hg hcg μ hK hμ] with x hx
  rw [← hx]
  exact (summable_of_sum_le (fun i => mul_nonneg i.2.le (sq_nonneg _))
    (fun s => coherentOrbital_density_le hg.continuous hcg μ hK hμ s x)).hasSum

lemma coherentOrbital_weight_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {W : Space → ℝ} (hW : AEStronglyMeasurable W volume)
    (hWi : Integrable (fun x => |W x| *coherentDensity g μ x)) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
        W x * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
      (∫ x : Space, W x * coherentDensity g μ x) := by
  have h := nonneg_series_weight_hasSum volume
    (f := fun (i : CoherentPositiveIndex hg.continuous hcg μ) (x : Space) =>
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
    (fun i => continuous_const.mul ((coherentOrbital_smooth hg hcg μ hK hμ i.1).continuous.norm.pow 2)
      |>.aestronglyMeasurable)
    (fun i _ => mul_nonneg i.2.le (sq_nonneg _)) hW hWi
    (coherentOrbital_density_hasSum hg hcg μ hK hμ)
  simpa only [mul_left_comm (W _) (coherentWeight _ _ _ _),integral_const_mul] using h

lemma coherentDensity_bounded_weight_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {W : Space → ℝ} (hW : AEStronglyMeasurable W volume) {C : ℝ}
    (hb : ∀ x ∈ coherentSpatialSupport g K, |W x| ≤ C) :
    Integrable (fun x => |W x| *coherentDensity g μ x) := by
  apply ((coherentDensity_integrable hg hcg μ hK hμ).const_mul C).mono'
    (hW.norm.mul (coherentDensity_continuous hg μ hK hμ).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply,Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (coherentDensity_nonneg g μ x))]
  by_cases hx : x ∈ coherentSpatialSupport g K
  · exact mul_le_mul_of_nonneg_right (hb x hx) (coherentDensity_nonneg g μ x)
  · simp only [coherentDensity_zero_outside μ hμ hx,mul_zero,le_refl]

end CoulombAtom

end

end OAI
