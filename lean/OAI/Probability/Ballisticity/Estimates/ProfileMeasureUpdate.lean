import Mathlib
import OAI.Probability.Ballisticity.Estimates.ProperProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma measure_le_of_atoms {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {μ ν : Measure X} (h : ∀ x, μ {x}≤ν {x}) : μ≤ν := by
  apply Measure.le_iff.mpr
  intro s hs
  conv_lhs => rw [←μ.sum_smul_dirac]
  conv_rhs => rw [←ν.sum_smul_dirac]
  simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
  apply ENNReal.tsum_le_tsum
  intro x
  exact mul_le_mul (h x) le_rfl zero_le zero_le

noncomputable def arrayProfileMeasure {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (Y : ActualEpisodeArray e) : Measure (HorizontalSpace e) :=
  Measure.sum (fun z => arrayProfileMass e j p z Y • Measure.dirac z)

lemma arrayProfileMeasure_atom {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (Y : ActualEpisodeArray e) (z : HorizontalSpace e) :
    arrayProfileMeasure e j p Y {z}=arrayProfileMass e j p z Y :=
  Measure.sum_smul_dirac_singleton

lemma arrayProfileImage {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (Y : ActualEpisodeArray e) (A : Set (HorizontalSpace e)) :
    (upperHorizontalKernel e H (arrayUpperRows e i m a Y) ∘ₘ arrayProfileMeasure e i (i,a) Y) A=
      arrayKernelImage e i m a H A Y := by
  rw [Measure.comp_eq_sum_of_countable,Measure.sum_apply _ (Set.to_countable A).measurableSet]
  simp only [Measure.smul_apply,smul_eq_mul,arrayProfileMeasure_atom]
  rfl

lemma arrayProfile_measure_update {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (Y : ActualEpisodeArray e) (hc : ArrayContinuation e Y) (hh : arrayWindowHeight e i m Y=H) :
    upperHorizontalKernel e H (arrayUpperRows e i m a Y) ∘ₘ arrayProfileMeasure e i (i,a) Y ≤
      expNeg (arrayWindowCost e i m Y) • arrayProfileMeasure e (i+m) (i,a) Y := by
  apply measure_le_of_atoms
  intro z
  rw [arrayProfileImage,Measure.smul_apply,smul_eq_mul,arrayProfileMeasure_atom]
  exact hc i m a H z hh

lemma properProfileKernel_eq_map {d : ℕ} (e : Direction d) (w : ProperProfile e) :
    properProfileKernel e w=(Measure.sum (fun z => w.1 z • Measure.dirac z)).map (horizontalLayerEquiv e) := by
  rw [Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]
  rfl

lemma properData_kernel_eq {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedArray e)
    (hp : IsProperProfile e (markedProfile e (markedData e p))) :
    properProfileKernel e (properData e w₀ (markedData e p))=
      (arrayProfileMeasure e 0 (0,p.2) p.1).map (horizontalLayerEquiv e) := by
  rw [properProfileKernel_eq_map,properData_eq _ _ _ hp]
  rfl

lemma horizontalKernel_fill {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (H : ℕ) (ξ : UpperRows e) (ω : Environment d) (z : HorizontalSpace e) :
    horizontalCoordinateKernel e f H (fillUpper e (ξ,ω)) (horizontalLayerEquiv e z)=
      (upperHorizontalKernel e H ξ z).map (fun x => x.1 f) := by
  rw [horizontalCoordinateKernel_apply]
  change (hitKernel (Strip _ z.val H) (Upper _ z.val H) (fillUpper e (ξ,ω),z.val)).map _=
    ((variableHitKernel _ H (upperEnvironment e ξ,horizontalLift e 0 z)).map (horizontalProjection e)).map _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hz : horizontalLift e 0 z=z.val := by simp [horizontalLift]
  rw [hz]
  have hk : hitKernel (Strip (realPosition (step e)) z.val H) (Upper (realPosition (step e)) z.val H)
      (fillUpper e (ξ,ω),z.val)=
      hitKernel (Strip (realPosition (step e)) z.val H) (Upper (realPosition (step e)) z.val H)
      (upperEnvironment e ξ,z.val) := by
    apply hitKernel_congr
    intro x hx
    apply fillUpper_eq
    have h0 : dot (realPosition z.val) (realPosition (step e))=0 := by
      rw [signedHeight_projection]
      have hz0 : z.val e.1=0 := z.property
      simp [signedHeight,hz0]
    have hh := hx.1
    rw [h0,signedHeight_projection] at hh
    exact_mod_cast hh
  rw [hk]
  apply congrArg (fun k => Measure.map k (hitKernel (Strip (realPosition (step e)) z.val H)
    (Upper (realPosition (step e)) z.val H) (upperEnvironment e ξ,z.val)))
  funext x
  simp [Function.comp_apply,horizontalProjection,Ne.symm hef]

lemma horizontalProfileImage_fill {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (H : ℕ) (ξ : UpperRows e) (ω : Environment d) (μ : Measure (HorizontalSpace e)) :
    horizontalCoordinateKernel e f H (fillUpper e (ξ,ω)) ∘ₘ μ.map (horizontalLayerEquiv e)=
      (upperHorizontalKernel e H ξ ∘ₘ μ).map (fun x => x.1 f) := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((horizontalCoordinateKernel e f H (fillUpper e (ξ,ω))).measurable_coe hA)
      (measurable_of_countable _),Measure.map_apply (measurable_of_countable _) hA,
    Measure.bind_apply ((measurable_of_countable _) hA) (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro z
  rw [horizontalKernel_fill e f hef,Measure.map_apply (measurable_of_countable _) hA]

end DirectionalTransience

end

end OAI
