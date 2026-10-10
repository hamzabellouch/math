import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_coordinate_of_gaussianArray
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → ℝ≥0 → Ω → ℝ}
    (hG : IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => B p.1 p.2) P)
    (hmean : ∀ i t, ∫ ω, B i t ω ∂P = 0)
    (hcov : ∀ i s t, s ≤ t → cov[B i s, B i t; P] = (s : ℝ))
    (i : ι) : IsPreBrownianReal (B i) P := by
  have hGi : IsGaussianProcess (B i) P := hG.comp_right (Sigma.mk i)
  exact hGi.isPreBrownianReal_of_covariance (hmean i) (hcov i)

theorem iIndepFun_of_gaussianArray_crossCovariance
    {ι Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → T → Ω → ℝ}
    (hG : IsGaussianProcess (fun p : (_ : ι) × T => B p.1 p.2) P)
    (hcross : ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0) :
    iIndepFun (fun i ω t => B i t ω) P := by
  exact hG.iIndepFun_of_covariance_eq_zero
    (fun i t => hG.aemeasurable ⟨i, t⟩) hcross

theorem map_gaussianArray_eq_infinitePi
    {ι Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → T → Ω → ℝ}
    (hG : IsGaussianProcess (fun p : (_ : ι) × T => B p.1 p.2) P)
    (hm : ∀ i t, Measurable (B i t))
    (hcross : ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0) :
    P.map (fun ω i t => B i t ω) =
      Measure.infinitePi (fun i => P.map (fun ω t => B i t ω)) := by
  exact (iIndepFun_of_gaussianArray_crossCovariance hG hcross).map_fun_eq_infinitePi_map
    (fun i => Measurable.of_eval (hm i))

theorem map_preBrownian_process_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (hmB : ∀ t, Measurable (B t)) (hmC : ∀ t, Measurable (C t)) :
    P.map (fun ω t => B t ω) = Q.map (fun ω t => C t ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure Q := hC.isGaussianProcess.isProbabilityMeasure
  have hp : IsProjectiveLimit (P.map (fun ω t => B t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval hmB)]
    exact (hB.hasLaw I).map_eq
  have hq : IsProjectiveLimit (Q.map (fun ω t => C t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval hmC)]
    exact (hC.hasLaw I).map_eq
  exact hp.unique hq

theorem map_brownianArray_eq_infinitePi_reference
    {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {B : ι → ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (hG : IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => B p.1 p.2) P)
    (hmB : ∀ i t, Measurable (B i t))
    (hmean : ∀ i t, ∫ ω, B i t ω ∂P = 0)
    (hcov : ∀ i s t, s ≤ t → cov[B i s, B i t; P] = (s : ℝ))
    (hcross : ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0)
    (hC : IsPreBrownianReal C Q) (hmC : ∀ t, Measurable (C t)) :
    P.map (fun ω i t => B i t ω) =
      Measure.infinitePi (fun _ : ι => Q.map (fun ω t => C t ω)) := by
  rw [map_gaussianArray_eq_infinitePi hG hmB hcross]
  congr 1
  funext i
  exact map_preBrownian_process_eq
    (preBrownian_coordinate_of_gaussianArray hG hmean hcov i) hC (hmB i) hmC

theorem iIndepFun_of_measurableEmbedding
    {ι Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] {P : Measure Ω} {X : ι → Ω → E}
    {e : E → F} (he : MeasurableEmbedding e)
    (h : iIndepFun (fun i => e ∘ X i) P) : iIndepFun X P := by
  rw [iIndepFun_iff_iIndep] at h ⊢
  simpa only [← MeasurableSpace.comap_comp, he.comap_eq] using h

section ContinuousPaths

variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
  [Nonempty T] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

theorem measurableEmbedding_continuousPath_denseSeq :
    MeasurableEmbedding
      (fun (f : C(T, ℝ)) n => f (TopologicalSpace.denseSeq T n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun _ => (continuous_eval_const _).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq T).equalizer f.continuous g.continuous h

theorem measurable_continuousPath_of_evaluations
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → C(T, ℝ)}
    (hm : ∀ t, Measurable (fun ω => X ω t)) : Measurable X := by
  apply measurableEmbedding_continuousPath_denseSeq.measurable_comp_iff.mp
  exact Measurable.of_eval (fun index => hm (TopologicalSpace.denseSeq T index))

theorem iIndepFun_continuousPaths_of_evaluations
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → C(T, ℝ)}
    (h : iIndepFun (fun i ω t => X i ω t) P) : iIndepFun X P := by
  apply iIndepFun_of_measurableEmbedding measurableEmbedding_continuousPath_denseSeq
  exact h.comp (fun _ f n => f (TopologicalSpace.denseSeq T n))
    (fun _ => Measurable.of_eval (fun _ => measurable_pi_apply _))

theorem map_continuousPaths_eq_of_evaluations
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → C(T, ℝ)} {Y : Ω' → C(T, ℝ)}
    (hmX : Measurable X) (hmY : Measurable Y)
    (h : P.map (fun ω t => X ω t) = Q.map (fun ω t => Y ω t)) :
    P.map X = Q.map Y := by
  apply measurableEmbedding_continuousPath_denseSeq.map_injective
  rw [Measure.map_map measurableEmbedding_continuousPath_denseSeq.measurable hmX,
    Measure.map_map measurableEmbedding_continuousPath_denseSeq.measurable hmY]
  have hs : Measurable (fun f : T → ℝ => fun n => f (TopologicalSpace.denseSeq T n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hX : Measurable (fun ω t => X ω t) :=
    Measurable.of_eval (fun time => (continuous_eval_const time).measurable.comp hmX)
  have hY : Measurable (fun ω t => Y ω t) :=
    Measurable.of_eval (fun time => (continuous_eval_const time).measurable.comp hmY)
  have hh := congrArg
    (Measure.map (fun f : T → ℝ => fun n => f (TopologicalSpace.denseSeq T n))) h
  simpa only [Measure.map_map hs hX, Measure.map_map hs hY, Function.comp_def] using hh

end ContinuousPaths

section ContinuousBrownianPaths

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
  [StandardBorelSpace C(ℝ≥0, ℝ)]

theorem map_continuousPreBrownian_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → C(ℝ≥0, ℝ)} {Y : Ω' → C(ℝ≥0, ℝ)}
    (hmX : Measurable X) (hmY : Measurable Y)
    (hX : IsPreBrownianReal (fun t ω => X ω t) P)
    (hY : IsPreBrownianReal (fun t ω => Y ω t) Q) :
    P.map X = Q.map Y := by
  apply map_continuousPaths_eq_of_evaluations hmX hmY
  exact map_preBrownian_process_eq hX hY
    (fun t => (continuous_eval_const t).measurable.comp hmX)
    (fun t => (continuous_eval_const t).measurable.comp hmY)

theorem map_continuousBrownianArray_eq_infinitePi_reference
    {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : ι → Ω → C(ℝ≥0, ℝ)} {Y : Ω' → C(ℝ≥0, ℝ)}
    (hmX : ∀ i, Measurable (X i)) (hmY : Measurable Y)
    (hG : IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => fun ω => X p.1 ω p.2) P)
    (hmean : ∀ i t, ∫ ω, X i ω t ∂P = 0)
    (hcov : ∀ i s t, s ≤ t → cov[fun ω => X i ω s, fun ω => X i ω t; P] = (s : ℝ))
    (hcross : ∀ i j, i ≠ j → ∀ s t,
      cov[fun ω => X i ω s, fun ω => X j ω t; P] = 0)
    (hY : IsPreBrownianReal (fun t ω => Y ω t) Q) :
    P.map (fun ω i => X i ω) =
      Measure.infinitePi (fun _ : ι => Q.map Y) := by
  have hi : iIndepFun X P := iIndepFun_continuousPaths_of_evaluations
    (iIndepFun_of_gaussianArray_crossCovariance hG hcross)
  rw [hi.map_fun_eq_infinitePi_map hmX]
  congr 1
  funext i
  exact map_continuousPreBrownian_eq (hmX i) hmY
    (preBrownian_coordinate_of_gaussianArray hG hmean hcov i) hY

end ContinuousBrownianPaths

end Problem367

end

end OAI
