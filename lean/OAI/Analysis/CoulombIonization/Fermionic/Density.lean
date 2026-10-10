import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FermionDensityMass

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

def density {N : ℕ} (ψ : FormVector (N+1)) (hψ : ∀ s, MemLp (ψ.value s) 2) (x : Space) : ℝ :=
  (oneParticleDensity ψ hψ x).toReal

lemma density_nonneg {N : ℕ} (ψ : FormVector (N+1)) (hψ : ∀ s, MemLp (ψ.value s) 2) (x : Space) :
    0 ≤ density ψ hψ x := ENNReal.toReal_nonneg

lemma density_integrable {N : ℕ} (ψ : FormVector (N+1)) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    Integrable (density ψ hψ) := fermionDensity_real_integrable (toMany ψ hψ)

lemma density_mass {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    (∫ x, density ψ hψ.1 x) = (N+1:ℝ) := by
  change (∫ x, (fermionDensity (toMany ψ hψ.1) x).toReal) = _
  rw [fermionDensity_real_mass,toMany_norm_sq,hψ.2.2.2.2.1,mul_one]

lemma density_power_integrable {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    Integrable (fun x => density ψ hψ.1 x^(5/3:ℝ)) := by
  have hm := (fermionDensity_aemeasurable (toMany ψ hψ.1)).pow_const (5/3:ℝ)
  have hb := form_lieb_thirring ψ hψ
  have hn : (∫⁻ x, oneParticleDensity ψ hψ.1 x^(5/3:ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hi := integrable_toReal_of_lintegral_ne_top hm hn
  change Integrable (fun x => (fermionDensity (toMany ψ hψ.1) x).toReal ^ (5/3:ℝ))
  simpa only [← ENNReal.toReal_rpow] using hi

lemma density_power_bound {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    (∫ x, density ψ hψ.1 x^(5/3:ℝ)) ≤
      32*(N+1:ℝ) + (2048/3:ℝ) *
        (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
          ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2) := by
  have hm := (fermionDensity_aemeasurable (toMany ψ hψ.1)).pow_const (5/3:ℝ)
  have hb := form_lieb_thirring ψ hψ
  have hn : (∫⁻ x, oneParticleDensity ψ hψ.1 x^(5/3:ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have he := integral_toReal hm (ae_lt_top' hm hn)
  simp only [← ENNReal.toReal_rpow] at he
  change (∫ x, (fermionDensity (toMany ψ hψ.1) x).toReal ^ (5/3:ℝ)) ≤ _
  rw [he]
  exact (ENNReal.toReal_le_toReal hn ENNReal.ofReal_ne_top).2 hb |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))

lemma toMany_coordinate_lintegral {N : ℕ} (ψ : FormVector N)
    (hψ : ∀ s, MemLp (ψ.value s) 2) (i : Fin N) (w : Space → ℝ)
    (hw : Measurable w) :
    (∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖toMany ψ hψ q‖^2)
      ∂configMeasure N oneMeasure) =
    ∑ s : Spins N, ∫⁻ x : Configuration N,
      ENNReal.ofReal (w (x i)) * ENNReal.ofReal (‖ψ.value s x‖^2) := by
  have hm : AEMeasurable (fun p : Configuration N × Spins N =>
      ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2))
      ((volume : Measure (Configuration N)).prod Measure.count) :=
    ((hw.comp ((measurable_pi_apply i).comp measurable_fst)).ennreal_ofReal.aemeasurable).mul
      ((memLp_spin ψ.value hψ).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  calc
    _ = ∫⁻ q, ENNReal.ofReal (w (q i).1) *
        ENNReal.ofReal (‖ψ.value (fun j => (q j).2) (fun j => (q j).1)‖^2)
          ∂configMeasure N oneMeasure := by
      apply lintegral_congr_ae
      filter_upwards [toMany_ae ψ hψ] with q hq
      rw [hq]
    _ = ∫⁻ p : Configuration N × Spins N,
        ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2)
        ∂volume.prod Measure.count :=
      (splitSpin_preserving N).lintegral_comp_emb (splitSpin N).measurableEmbedding
        (fun p : Configuration N × Spins N => ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2))
    _ = _ := by
      rw [lintegral_prod_symm _ hm]
      simp only [lintegral_fintype,Measure.count_singleton,mul_one]

lemma density_coulomb_lintegral {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    (∫⁻ x, ENNReal.ofReal (‖x‖⁻¹) * oneParticleDensity ψ hψ.1 x) =
    ENNReal.ofReal (∑ s : Spins (N+1), ∑ i : Fin (N+1),
      ∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖) := by
  change (∫⁻ x : Space, ENNReal.ofReal (‖x‖⁻¹) * fermionDensity (toMany ψ hψ.1) x) = _
  rw [density_weighted_lintegral (toMany ψ hψ.1) (fun x : Space => ‖x‖⁻¹) measurable_norm.inv]
  trans ∑ i : Fin (N+1), ∑ s : Spins (N+1), ∫⁻ x : Configuration (N+1),
    ENNReal.ofReal (‖x i‖⁻¹) * ENNReal.ofReal (‖ψ.value s x‖^2)
  · exact Finset.sum_congr rfl (fun i _ =>
      toMany_coordinate_lintegral ψ hψ.1 i (fun x : Space => ‖x‖⁻¹) measurable_norm.inv)
  have hi (i : Fin (N+1)) (s : Spins (N+1)) :
      (∫⁻ x : Configuration (N+1), ENNReal.ofReal (‖x i‖⁻¹) *
        ENNReal.ofReal (‖ψ.value s x‖^2)) =
      ENNReal.ofReal (∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hψ.2.2.2.2.2.1 s i)
      (Filter.Eventually.of_forall (fun x => by positivity))]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ‖x i‖⁻¹)]
    congr 1
    simp only [div_eq_mul_inv,mul_comm]
  simp_rw [hi]
  rw [Finset.sum_comm]
  have hnuc (s : Spins (N+1)) (i : Fin (N+1)) :
      0 ≤ ∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖ :=
    integral_nonneg (fun _ => by positivity)
  have heach (s : Spins (N+1)) :
      (∑ i : Fin (N+1), ENNReal.ofReal (∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖)) =
      ENNReal.ofReal (∑ i : Fin (N+1), ∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖) :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnuc s i)).symm
  simp_rw [heach]
  exact (ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg
    (fun i _ => hnuc s i))).symm

lemma density_coulomb_integral {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    Integrable (fun x => density ψ hψ.1 x / ‖x‖) ∧
    (∫ x, density ψ hψ.1 x / ‖x‖) =
      ∑ s : Spins (N+1), ∑ i : Fin (N+1),
        ∫ x : Configuration (N+1), ‖ψ.value s x‖^2 / ‖x i‖ := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (‖x‖⁻¹) * oneParticleDensity ψ hψ.1 x) :=
    measurable_norm.inv.ennreal_ofReal.aemeasurable.mul
      (fermionDensity_aemeasurable (toMany ψ hψ.1))
  have he := density_coulomb_lintegral ψ hψ
  have hn : (∫⁻ x, ENNReal.ofReal (‖x‖⁻¹) * oneParticleDensity ψ hψ.1 x) ≠ ⊤ := by
    rw [he]; exact ENNReal.ofReal_ne_top
  have hv (x : Space) :
      (ENNReal.ofReal (‖x‖⁻¹) * oneParticleDensity ψ hψ.1 x).toReal = density ψ hψ.1 x/‖x‖ := by
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
    exact mul_comm _ _
  have hit := integrable_toReal_of_lintegral_ne_top hm hn
  have hei := integral_toReal hm (ae_lt_top' hm hn)
  simp only [hv] at hit hei
  refine ⟨hit, ?_⟩
  rw [hei,he,ENNReal.toReal_ofReal (by positivity)]
end CoulombAtom.Pauli

open MeasureTheory Set Metric
open scoped ENNReal

end

end OAI
