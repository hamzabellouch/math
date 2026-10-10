import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPathWeight

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma permuteConfiguration_continuous {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n)) :
    Continuous (permuteConfiguration (L:=L) σ) := by
  unfold permuteConfiguration
  fun_prop

def permuteConfigurationPath {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n))
    (ω : ConfigurationPath n L) : ConfigurationPath n L :=
  ⟨fun s ↦ permuteConfiguration σ (ω s), (permuteConfiguration_continuous σ).comp ω.continuous⟩

lemma permuteConfigurationPath_continuous {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n)) :
    Continuous (permuteConfigurationPath (L:=L) σ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L × Time ↦ fun i ↦ p.1 p.2 (σ i))
  fun_prop

def permuteCoordinatePaths {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : CoordinatePaths n) : CoordinatePaths n := fun p ↦ w (σ p.1,p.2)

lemma permuteCoordinatePaths_preserving {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteCoordinatePaths σ) (coordinateWiener n) (coordinateWiener n) := by
  have h := measurePreserving_piCongrLeft (fun _ : Direction n ↦ wiener)
    (σ.symm.prodCongr (Equiv.refl (Fin 3)))
  convert h using 1 <;> try rfl
  funext w p
  simp [permuteCoordinatePaths,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast]
  rfl

lemma freeTrajectory_permute {n : ℕ} (L : Length) (t : ℝ) (σ : Equiv.Perm (Fin n))
    (w : CoordinatePaths n) (X : Configuration n L) :
    freeTrajectory n L t (permuteCoordinatePaths σ w) (permuteConfiguration σ X)=
      permuteConfigurationPath σ (freeTrajectory n L t w X) := rfl

lemma permute_freePath_preserving {n : ℕ} (L : Length) (t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (freePathLaw n L t) (freePathLaw n L t) := by
  refine ⟨(permuteConfigurationPath_continuous σ).measurable,?_⟩
  have h := (permuteCoordinatePaths_preserving σ).prod (measurePreserving_permute (L:=L) σ)
  rw [freePathLaw,Measure.map_map (permuteConfigurationPath_continuous σ).measurable
    (freeTrajectory_continuous n L t).measurable]
  conv_rhs => rw [←h.map_eq]
  rw [Measure.map_map (freeTrajectory_continuous n L t).measurable h.measurable]
  rfl

lemma permute_staysAllowed {n : ℕ} (L : Length) (r : ℝ) (σ : Equiv.Perm (Fin n)) :
    permuteConfigurationPath σ ⁻¹' staysAllowed n L r = staysAllowed n L r := by
  ext ω
  simp only [Set.mem_preimage,staysAllowed,Set.mem_ofPred_eq,Set.range_subset_iff]
  constructor
  · intro h s
    exact (allowed_permute σ (ω s)).mp (h s)
  · intro h s
    exact (allowed_permute σ (ω s)).mpr (h s)

lemma permute_killedPath_preserving {n : ℕ} (L : Length) (r t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (killedPathLaw n L r t) (killedPathLaw n L r t) := by
  have h := (permute_freePath_preserving L t σ).restrict_preimage (staysAllowed_open n L r).measurableSet
  rw [permute_staysAllowed] at h
  exact h

lemma measurePreserving_weighted_ae_invariant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : α → α} (hR : MeasurePreserving R μ μ)
    (w : α → ℝ≥0∞) (hw : Measurable w) (hi : (fun x ↦ w (R x)) =ᵐ[μ] w) :
    MeasurePreserving R (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hR.measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply hR.measurable hS,withDensity_apply _ (hS.preimage hR.measurable),
    withDensity_apply _ hS,←lintegral_indicator (hS.preimage hR.measurable),←lintegral_indicator hS]
  calc
    _ = ∫⁻ x, (S.indicator w) (R x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hi] with x hx
      by_cases h : R x∈S
      · simp only [Set.indicator_of_mem h,Set.indicator_of_mem (show x∈R ⁻¹' S from h),hx]
      · simp only [Set.indicator_of_notMem h,Set.indicator_of_notMem (show x∉R ⁻¹' S from h)]
    _ = _ := hR.lintegral_comp (hw.indicator hS)

lemma groundPositionLaw_permute {n : ℕ} {L : Length} (u : Jet n L) (hb : bosonic u.1)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfiguration σ) (groundPositionLaw n L u) (groundPositionLaw n L u) := by
  apply measurePreserving_weighted_ae_invariant (measurePreserving_permute σ) _
    ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
  filter_upwards [hb σ] with X hX
  change ENNReal.ofReal (‖u.1 (fun i ↦ X (σ i))‖^2)=ENNReal.ofReal (‖u.1 X‖^2)
  rw [hX]

lemma groundPathLaw_permute {n : ℕ} {L : Length} (u : Jet n L) (hb : bosonic u.1)
    (r t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (groundPathLaw n L r t u) (groundPathLaw n L r t u) := by
  apply measurePreserving_weighted_ae_invariant (permute_killedPath_preserving L r t σ) _
    (groundPathWeight_measurable u t).ennreal_ofReal
  have hp (s : Time) := (((freePathLaw_marginal n L t s).quasiMeasurePreserving.ae_eq_comp
    (hb σ)).filter_mono (ae_mono (Measure.restrict_le_self (s:=staysAllowed n L r))))
  filter_upwards [hp 0,hp 1] with ω h0 h1
  simp only [Function.comp_def] at h0 h1
  change ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 (fun i ↦ ω 0 (σ i))‖*
    ‖u.1 (fun i ↦ ω 1 (σ i))‖))=ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 (ω 0)‖*‖u.1 (ω 1)‖))
  rw [h0,h1]

end HardSphere

end
end

end

end OAI
