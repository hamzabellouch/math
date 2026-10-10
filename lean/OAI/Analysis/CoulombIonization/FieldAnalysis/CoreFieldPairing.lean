import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketDensity
import OAI.Analysis.CoulombIonization.Variational.CompactPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma core_density_product_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    Integrable (fun r : Configuration N × Space => ‖ψ.value s r.1‖^2 * ρ r.2 / ‖r.1 i-r.2‖) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have ha : AEStronglyMeasurable
      (fun r : Configuration N × Space => ‖ψ.value s r.1‖^2 * ρ r.2 / ‖r.1 i-r.2‖) volume := by
    have hnorm : Measurable (fun r : Configuration N × Space => ‖r.1 i-r.2‖⁻¹) := by fun_prop
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.pow_apply,Measure.volume_eq_prod] using
      (((hψ.1 s).aestronglyMeasurable.norm.pow 2).comp_fst.fun_mul hm.aestronglyMeasurable.comp_snd).fun_mul
        hnorm.aestronglyMeasurable
  apply (integrable_prod_iff ha).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable h1 hp (x i)).const_mul (‖ψ.value s x‖^2)
  · obtain ⟨C,hC⟩ := compact_support_potential_bounded h1.norm hp.norm hJ
      (fun x hx => hs (by intro hz; exact hx (by simp [hz])))
    have hi := core_bounded_potential_integrable hψ
      (CoulombAnalysis.tfPotential_continuous h1.norm hp.norm) hC s i
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg _),norm_norm,
      CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma core_density_coordinate_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    (∫ x : Configuration N, ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential ρ (x i)) =
      ∫ y : Space, ρ y*(∫ x : Configuration N, ‖ψ.value s x‖^2/‖x i-y‖) := by
  have hi := core_density_product_integrable hψ hm hJ hs hb s i
  have hh := integral_integral_swap (f := fun x y => ‖ψ.value s x‖^2 * ρ y / ‖x i-y‖) hi
  simp only [CoulombAnalysis.tfPotential,← integral_const_mul] at ⊢
  convert hh using 1 <;> (congr 1; funext x; congr 1; funext y; ring)

lemma core_density_coordinate_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    Integrable (fun y : Space => ρ y*(∫ x : Configuration N, ‖ψ.value s x‖^2/‖x i-y‖)) := by
  have hi := (core_density_product_integrable hψ hm hJ hs hb s i).integral_prod_right
  convert hi using 1
  funext y
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem coreDensityInteraction_eq_field {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) :
    coreDensityInteraction ψ ρ = ∫ y : Space, ρ y*coreCoulombAt ψ y := by
  unfold coreDensityInteraction coreCoulombAt
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
    core_density_coordinate_integrable hψ hm hJ hs hb s i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun i _ => core_density_coordinate_integrable hψ hm hJ hs hb s i)]
  exact Finset.sum_congr rfl (fun i _ => core_density_coordinate_pairing hψ hm hJ hs hb s i)

lemma coreDensityField_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) :
    Integrable (fun y : Space => ρ y*coreCoulombAt ψ y) := by
  simp only [coreCoulombAt,Finset.mul_sum]
  exact integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
    core_density_coordinate_integrable hψ hm hJ hs hb s i))

end CoulombAtom

end

end OAI
