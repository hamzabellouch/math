import Mathlib
import OAI.Analysis.HardSphere.Fourier.ArgumentAdd

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener ProbabilityTheory
open scoped ComplexConjugate

lemma wiener_initial_zero : ∀ᵐ w : C(Time,ℝ) ∂wiener, w 0 = 0 := by
  rw [wiener, ae_map_iff measurable_path.aemeasurable
    (isClosed_eq (continuous_eval_const (0:Time)) continuous_const).measurableSet]
  exact Filter.Eventually.of_forall path_at_zero

lemma coordinateWiener_initial_zero (N : ℕ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ p, w p 0 = 0 := by
  apply ae_all_iff.mpr
  intro p
  exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).quasiMeasurePreserving.ae wiener_initial_zero

lemma freeTrajectory_initial_ae (N : ℕ) (L : Length) (t : ℝ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ X, freeTrajectory N L t w X 0 = X := by
  filter_upwards [coordinateWiener_initial_zero N] with w hw X
  ext i j
  simp only [freeTrajectory, ContinuousMap.coe_mk, hw (i,j), mul_zero,
    QuotientAddGroup.mk_zero, add_zero]

def freeTransition (N : ℕ) (L : Length) (t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (endpointPull N L t 1).toContinuousLinearMap

lemma freeTransition_pairing (N : ℕ) (L : Length) (t : ℝ) (f g : ScalarL2 N L) :
    inner ℂ f (freeTransition N L t g) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂freePathLaw N L t := by
  rw [freeTransition, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [endpointPull_ae N L t 0 f, endpointPull_ae N L t 1 g] with ω hf hg
  change inner ℂ ((endpointPull N L t 0) f ω) ((endpointPull N L t 1) g ω) = _
  rw [hf,hg,RCLike.inner_apply,mul_comm]

lemma freeTransition_continuous_pairing (N : ℕ) (L : Length) (t : ℝ)
    (f g : C(Configuration N L,ℂ)) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f)
      (freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂freePathLaw N L t := by
  rw [freeTransition_pairing]
  apply integral_congr_ae
  filter_upwards [(freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f),
    (freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g)] with ω hf hg
  rw [hf,hg]

lemma integrable_free_character (N : ℕ) (L : Length) (t : ℝ)
    (f : C(Configuration N L,ℂ)) (k : Direction N → ℤ) :
    Integrable (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1))
      ((coordinateWiener N).prod volume) := by
  have hc : Continuous (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) := by
    exact (f.continuous.comp continuous_snd).star.mul
      ((configurationCharacter N L k).continuous.comp
        ((freeTrajectory_continuous N L t).eval continuous_const))
  refine (integrable_const ‖f‖).mono' hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [norm_mul, RCLike.norm_conj, configurationCharacter_norm, mul_one]
    exact f.norm_coe_le_norm p.2

lemma freeTransition_character_pairing (N : ℕ) (L : Length) (t : ℝ) (ht : 0 ≤ t)
    (f : C(Configuration N L,ℂ)) (k : Direction N → ℤ) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (freeTransition N L t (characterL2 N L k)) =
      (Real.exp (-t * fourierEnergy N L k) : ℂ) *
        inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (characterL2 N L k) := by
  change inner ℂ _ (freeTransition N L t (ContinuousMap.toLp 2 volume ℂ _)) = _
  rw [freeTransition_continuous_pairing, freePathLaw]
  have hc : Continuous (fun ω : ConfigurationPath N L ↦
      conj (f (ω 0)) * configurationCharacter N L k (ω 1)) := by fun_prop
  rw [integral_map (freeTrajectory_continuous N L t).measurable.aemeasurable
    hc.aestronglyMeasurable]
  have hzero : (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f (freeTrajectory N L t p.1 p.2 0)) *
        configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) =ᵐ[
        (coordinateWiener N).prod volume]
      (fun p ↦ conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae N L t)] with p hp
    rw [hp]
  rw [integral_congr_ae hzero, integral_prod_symm _ (integrable_free_character N L t f k)]
  simp_rw [integral_const_mul, freeTrajectory_character_integral N L k t ht]
  rw [show (∫ X, conj (f X) * (configurationCharacter N L k X *
      (Real.exp (-t*fourierEnergy N L k) : ℂ))) =
      (Real.exp (-t*fourierEnergy N L k) : ℂ) *
        ∫ X, conj (f X) * configurationCharacter N L k X by
    rw [← integral_const_mul]; congr 1; ext X; ring]
  congr 1
  rw [characterL2, ContinuousMap.inner_toLp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦ mul_comm _ _

lemma freeTransition_character (N : ℕ) (L : Length) (t : ℝ) (ht : 0 ≤ t)
    (k : Direction N → ℤ) :
    freeTransition N L t (characterL2 N L k) =
      (Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k := by
  apply ext_inner_left ℂ
  intro f
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  have hc : IsClosed {f : ScalarL2 N L |
      inner ℂ f (freeTransition N L t (characterL2 N L k)) =
        inner ℂ f ((Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k)} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  have hz : ∀ f : C(Configuration N L,ℂ),
      inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (freeTransition N L t (characterL2 N L k)) =
        inner ℂ (ContinuousMap.toLp 2 volume ℂ f)
          ((Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k) := by
    intro f
    rw [freeTransition_character_pairing N L t ht, inner_smul_right]
  exact (hc.closure_subset_iff.mpr (Set.range_subset_iff.mpr hz)) (hd f)

end HardSphere

end

end OAI
