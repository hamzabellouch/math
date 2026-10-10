import OAI.Probability.StrongRayleigh.InnovationCharacteristicProcess
import OAI.Probability.StrongRayleigh.BrownianPathLaw

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem exists_measurable_iid_brownian_path_version
    {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    {X : I → ℝ≥0 → Ω → ℝ}
    (hpre : ∀ i, IsPreBrownianReal (X i) P)
    (hindep : iIndepFun (fun i ω t => X i t ω) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  let R : Ω → I → C(ℝ≥0, ℝ) :=
    fun ω i => ContinuousPathLaw.brownianPath (X i) ω
  have hBrown (i : I) : IsBrownianReal (X i) P := ⟨hpre i, hcont i⟩
  have hm : AEMeasurable R P :=
    AEMeasurable.of_eval fun i => ContinuousPathLaw.aemeasurable_brownianPath (hBrown i)
  have hrational : iIndepFun
      (fun i ω q => X i (ContinuousPathLaw.rationalTime q) ω) P :=
    hindep.comp (fun _ f q => f (ContinuousPathLaw.rationalTime q))
      (fun _ => Measurable.of_eval fun q => measurable_pi_apply _)
  have hcanon : ContinuousPathLaw.brownianPath
      (fun t (w : C(ℝ≥0, ℝ)) => w t) = id := by
    funext w
    apply ContinuousMap.coe_injective
    funext t
    simp only [ContinuousPathLaw.brownianPath,
      ContinuousMap.mkD_apply_of_continuous w.continuous, id_eq]
  have hlaw : Measure.map R P = Measure.infinitePi (fun _ : I => ν) := by
    have h := ContinuousPathLaw.map_brownianPath_family_eq_infinitePi hBrown hrational hν
    simpa only [hcanon, Measure.map_id] using h
  refine ⟨hm.mk R, hm.measurable_mk, ?_, ?_⟩
  · exact (Measure.map_congr hm.ae_eq_mk.symm).trans hlaw
  · filter_upwards [hm.ae_eq_mk, ae_all_iff.mpr hcont] with ω he hc
    intro i t
    rw [← he]
    simp only [R, ContinuousPathLaw.brownianPath,
      ContinuousMap.mkD_apply_of_continuous (hc i)]

theorem exists_iid_path_version_of_eventwise_characteristic
    {Ω : Type u_3} {I : Type u_4} [mΩ : MeasurableSpace Ω] [Countable I]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure C(ℝ≥0, ℝ))
    (hν : IsBrownianReal (fun t (w : C(ℝ≥0, ℝ)) => w t) ν)
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => X i t ω))
    (hchar : ∀ (S : Finset I) (u v : ℝ≥0), u ≤ v →
      ∀ A : Set Ω, MeasurableSet[H u] A → ∀ θ : S → ℝ,
        (∫ ω in A, Complex.exp
          (((∑ i : S, θ i * (X i v ω - X i u ω) : ℝ) : ℂ) * Complex.I) ∂P) =
          ((P A).toReal : ℂ) * Complex.exp
            (- ((v - u : ℝ≥0) : ℂ) * ((∑ i : S, θ i ^ 2 : ℝ) : ℂ) / 2)) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      Measure.map W P = Measure.infinitePi (fun _ : I => ν) ∧
      ∀ᵐ ω ∂P, ∀ i t, W ω i t = X i t ω := by
  obtain ⟨hpre, hindep⟩ := independent_preBrownian_of_eventwise_characteristic H hX hzero hchar
  exact exists_measurable_iid_brownian_path_version ν hν hpre hindep hcont

end Problem336AdditiveD139

end

end OAI
