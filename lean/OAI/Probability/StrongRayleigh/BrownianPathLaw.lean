import OAI.Probability.StrongRayleigh.ContinuousPathLaw

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section

open MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace Problem336AdditiveD139.ContinuousPathLaw

section FiniteEvaluations

variable {Ω : Type u_1} {Ω' : Type u_2} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'}
variable {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}

theorem preBrownian_finite_eval_identDistrib
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    {J : Type u_3} [Fintype J] (t : J → ℝ≥0) :
    IdentDistrib (fun ω j => B (t j) ω) (fun ω j => C (t j) ω) P Q := by
  classical
  let S : Finset ℝ≥0 := Finset.univ.image t
  let r : (S → ℝ) → J → ℝ := fun f j => f ⟨t j, Finset.mem_image.mpr
    ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hr : Measurable r := Measurable.of_eval fun j => measurable_pi_apply _
  exact ((hB.hasLaw S).identDistrib (hC.hasLaw S)).comp hr

theorem preBrownian_rational_identDistrib
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q) :
    IdentDistrib (fun ω q => B (rationalTime q) ω)
      (fun ω q => C (rationalTime q) ω) P Q := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure Q := (hC.hasLaw_eval 0).isProbabilityMeasure
  have hmB : AEMeasurable (fun ω q => B (rationalTime q) ω) P :=
    AEMeasurable.of_eval fun q => hB.aemeasurable _
  have hmC : AEMeasurable (fun ω q => C (rationalTime q) ω) Q :=
    AEMeasurable.of_eval fun q => hC.aemeasurable _
  refine ⟨hmB, hmC, ?_⟩
  apply (isProjectiveLimit_map hmB).unique
  intro S
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict S).aemeasurable hmC]
  exact (preBrownian_finite_eval_identDistrib hB hC (fun q : S => rationalTime q)).map_eq.symm

end FiniteEvaluations

section ContinuousPaths

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

def rationalSamples (f : C(ℝ≥0, ℝ)) : ℚ → ℝ := fun q => f (rationalTime q)

theorem measurableEmbedding_rationalSamples : MeasurableEmbedding rationalSamples := by
  have hc : Continuous rationalSamples := continuous_pi fun q => continuous_eval_const _
  apply hc.measurableEmbedding
  intro f g h
  apply ContinuousMap.coe_injective
  exact denseRange_rationalTime.equalizer f.continuous g.continuous h

def brownianPath {Ω : Type u_4} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ContinuousMap.mkD (fun t => B t ω) 0

variable {Ω : Type u_5} {Ω' : Type u_6} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'}
variable {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}

omit [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)] in
theorem brownianPath_samples_ae_eq (hB : IsBrownianReal B P) :
    (rationalSamples ∘ brownianPath B) =ᵐ[P]
      (fun ω q => B (rationalTime q) ω) := by
  filter_upwards [hB.cont] with ω hω
  funext q
  simp only [Function.comp_apply, rationalSamples, brownianPath,
    ContinuousMap.mkD_apply_of_continuous hω]

theorem aemeasurable_brownianPath (hB : IsBrownianReal B P) :
    AEMeasurable (brownianPath B) P := by
  apply measurableEmbedding_rationalSamples.aemeasurable_comp_iff.mp
  exact (AEMeasurable.of_eval fun q => hB.aemeasurable (rationalTime q)).congr
    (brownianPath_samples_ae_eq hB).symm

theorem brownianPath_identDistrib (hB : IsBrownianReal B P) (hC : IsBrownianReal C Q) :
    IdentDistrib (brownianPath B) (brownianPath C) P Q := by
  refine ⟨aemeasurable_brownianPath hB, aemeasurable_brownianPath hC, ?_⟩
  apply measurableEmbedding_rationalSamples.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_rationalSamples.measurable.aemeasurable (aemeasurable_brownianPath hB),
    AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_rationalSamples.measurable.aemeasurable (aemeasurable_brownianPath hC)]
  exact (Measure.map_congr (brownianPath_samples_ae_eq hB)).trans
    ((preBrownian_rational_identDistrib hB.toIsPreBrownianReal hC.toIsPreBrownianReal).map_eq.trans
      (Measure.map_congr (brownianPath_samples_ae_eq hC)).symm)

theorem iIndepFun_paths_iff_rationalSamples {I : Type u_7}
    {X : I → Ω → C(ℝ≥0, ℝ)} :
    iIndepFun X P ↔ iIndepFun (fun i => rationalSamples ∘ X i) P := by
  constructor
  · intro h
    exact h.comp (fun _ => rationalSamples)
      (fun _ => measurableEmbedding_rationalSamples.measurable)
  · intro h
    have hi := h.comp (fun _ => measurableEmbedding_rationalSamples.invFun)
      (fun _ => measurableEmbedding_rationalSamples.measurable_invFun)
    convert hi using 1
    funext i ω
    exact (measurableEmbedding_rationalSamples.leftInverse_invFun (X i ω)).symm

theorem iIndepFun_brownianPath {I : Type u_8} {W : I → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) P)
    (hi : iIndepFun (fun i ω q => W i (rationalTime q) ω) P) :
    iIndepFun (fun i => brownianPath (W i)) P := by
  apply iIndepFun_paths_iff_rationalSamples.mpr
  exact iIndepFun.congr (fun i => (brownianPath_samples_ae_eq (hW i)).symm) hi

theorem map_brownianPath_family_eq_infinitePi {I : Type u_9} [Countable I]
    [IsProbabilityMeasure P] {W : I → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) P)
    (hi : iIndepFun (fun i ω q => W i (rationalTime q) ω) P)
    (hC : IsBrownianReal C Q) :
    P.map (fun ω i => brownianPath (W i) ω) =
      Measure.infinitePi (fun _ : I => Q.map (brownianPath C)) := by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀'
    (fun i => aemeasurable_brownianPath (hW i))).mp (iIndepFun_brownianPath hW hi)]
  congr 1
  funext i
  exact (brownianPath_identDistrib (hW i) hC).map_eq

end ContinuousPaths

end Problem336AdditiveD139.ContinuousPathLaw

end

end OAI
