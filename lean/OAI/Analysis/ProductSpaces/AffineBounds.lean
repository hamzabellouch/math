import OAI.Analysis.ProductSpaces.CoefficientLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uO uR uS uΛ uΩ uι

namespace IndependentProducts
section MeasureDiagram
variable {S : Type uS} {R : Type uR} {O : Type uO}
  [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace O]
variable {Ps : Measure S} {Pr : Measure R} {Po : Measure O} {q : S → R} {s : S → O}

lemma integral_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) : ∫ z, f z ∂Pr = ∫ ω, g ω ∂Po := by
  rw [← hq.hasLaw.integral_comp hf.aestronglyMeasurable,
    ← hs.hasLaw.integral_comp hg.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ he)

lemma integrable_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) (hi : Integrable g Po) : Integrable f Pr := by
  apply (hq.integrable_comp hf.aestronglyMeasurable).mp
  apply Integrable.congr ((hs.integrable_comp hg.aestronglyMeasurable).mpr hi)
  exact Filter.EventuallyEq.symm (ae_of_all Ps he)

end MeasureDiagram

lemma measurable_joint_firstExitSum {Λ : Type uΛ} {Ω : Type uΩ} {ι : Type uι}
    [MeasurableSpace Λ] [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (B : Λ → ι → Ω → ℝ)
    (hB : ∀ i, Measurable (fun z : Λ × Ω => B z.1 i z.2))
    (hm : ∀ i, Measurable (fun l => ∫ b, B l i b ∂ν)) :
    Measurable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1) := by
  unfold firstExitSum
  apply Finset.measurable_sum
  intro i hi
  exact (((hB i).comp
    (measurable_snd.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)))).mul
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))).sub
        ((hm i).comp measurable_snd)

namespace FiniteHead
section FiniteAffine
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (hmean : ∫ w : ℝ, w ∂μ = 1)
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)
variable (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (hv : ∀ k, (e (j k)).val.val <+: v k)

include h₂ hmean in
lemma measurable_tailCoefficient_mean (i : ι) :
    Measurable (fun old => ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ) := by
  classical
  have hm : Measurable (fun old => ∑ k, if j k = i then
      a k * pathProduct (e i).val.val.dropLast old else 0) := by
    apply Finset.measurable_sum
    intro k hk
    by_cases h : j k = i
    · simp only [h, ite_true]
      exact (measurable_pathProduct _).const_mul (a k)
    · simp only [h, ite_false]
      exact measurable_const
  have he : (fun old => ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ) =
      (fun old => ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0) :=
    funext (fun old => T.integral_tailCoefficient e v j a μ (h₂.integrable (by norm_num)) hmean old i)
  rw [he]
  exact hm

include h₂ hmean in
lemma measurable_resampled_tail :
    Measurable (fun z : ((ι → Sample) × (ι → ℝ)) × Sample =>
      firstExitSum (productMeasure μ) (T.tailCoefficient e v j a z.2) z.1) := by
  classical
  exact measurable_joint_firstExitSum (productMeasure μ) (T.tailCoefficient e v j a)
    (T.measurable_tailCoefficient e v j a)
    (measurable_tailCoefficient_mean μ h₂ hmean T e v j a)

lemma measurable_tailCoefficient_section (old : Sample) (i : ι) :
    Measurable (T.tailCoefficient e v j a old i) :=
  Measurable.of_uncurry_left (f := fun old desc => T.tailCoefficient e v j a old i desc)
    (T.measurable_tailCoefficient e v j a i)

include hmean he hv in
lemma affine_finite_polynomials (c : T.vertices → ℝ) (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      ‖∑ k, a k • T.relativeVector μ h₂ (v k)‖ -
      D * ‖∑ v : T.vertices, c v • pathVector μ h₂ v‖ ≤
      midpointGain t (∑ v : T.vertices, c v • pathVector μ h₂ v)
        (∑ k, a k • T.relativeVector μ h₂ (v k)) := by
  classical
  let P := productMeasure μ
  let Pb := Measure.pi (fun _ : ι => P)
  let Pw := Measure.pi (fun _ : ι => μ)
  let Ps := (Pb.prod P).prod P
  let Pr := (Pb.prod Pw).prod P
  let U : Sample → ℝ := fun old => ∑ v : T.vertices, c v * pathProduct v old
  let V : Sample → ℝ := fun ω => ∑ k, a k * (pathProduct (v k) ω - pathProduct (T.ancestor (v k)) ω)
  let B := T.tailCoefficient e v j a
  let Y : ((ι → Sample) × (ι → ℝ)) × Sample → ℝ := fun z => firstExitSum P (B z.2) z.1
  let q : ((ι → Sample) × Sample) × Sample → ((ι → Sample) × (ι → ℝ)) × Sample :=
    fun z => ((z.1.1, fun i => z.1.2 (e i).val), z.2)
  have hq : MeasurePreserving q Ps Pr :=
    ((MeasurePreserving.id Pb).prod (measurePreserving_coordinates μ (fun i => (e i).val)
      (Subtype.val_injective.comp he))).prod (MeasurePreserving.id P)
  have hst := T.measurePreserving_stitched e μ
  have hUm : Measurable U := Finset.measurable_sum _
    (fun v _ => (measurable_pathProduct v).const_mul (c v))
  have hVm : Measurable V := Finset.measurable_sum _
    (fun k _ => ((measurable_pathProduct (v k)).sub (measurable_pathProduct (T.ancestor (v k)))).const_mul (a k))
  have hYm : Measurable Y := T.measurable_resampled_tail μ h₂ hmean e v j a
  have heU : ∀ z : ((ι → Sample) × Sample) × Sample, U (q z).2 = U (T.stitched e z) := by
    intro z
    exact (T.stitched_head_polynomial e c z).symm
  have heY : ∀ z : ((ι → Sample) × Sample) × Sample, Y (q z) = V (T.stitched e z) := by
    intro z
    exact (T.stitched_tail_polynomial e v j a μ h₂ z he hv hmean).symm
  let x : productSpan μ := ∑ v : T.vertices, c v • pathVector μ h₂ v
  let y : productSpan μ := ∑ k, a k • T.relativeVector μ h₂ (v k)
  have hx : (x.val : Sample → ℝ) =ᵐ[P] U :=
    representative_sum μ (fun v : T.vertices => pathVector μ h₂ v)
      (fun v : T.vertices => pathProduct v) (fun v => pathVector_ae μ h₂ v) c
  have hy : (y.val : Sample → ℝ) =ᵐ[P] V :=
    representative_sum μ _ _ (fun k => T.relativeVector_ae μ h₂ (v k)) a
  have hUi : Integrable U P := integrable_rep μ x U hx
  have hVi : Integrable V P := integrable_rep μ y V hy
  have hYi : Integrable Y Pr := integrable_measure_diagram hq hst Y V hYm hVm heY hVi
  have hSi : Integrable (fun z : (ι → Sample) × Sample => euclidSize (fun i => B z.2 i (z.1 i)))
      (Pb.prod P) := integrable_euclidSize _ (T.integrable_tailCoefficient_all e v j a μ h₂)
  have hBi : ∀ old i, Integrable (B old i) P :=
    T.integrable_tailCoefficient e v j a μ (h₂.integrable (by norm_num))
  have hBm : ∀ old i, Measurable (B old i) := by
    intro old i
    exact measurable_tailCoefficient_section T e v j a old i
  have ha := integrated_first_exit_affine μ P P h₂ hmean B hBi hBm U hUi hSi hYi
    t A D hA hC hscalar
  have hnY : (∫ z, |Y z| ∂Pr) = ‖y‖ := by
    rw [integral_measure_diagram hq hst (fun z => |Y z|) (fun ω => |V ω|)
      hYm.abs hVm.abs (fun z => congrArg abs (heY z))]
    exact (norm_eq_integral_abs_rep μ y V hy).symm
  have hnU : (∫ old, |U old| ∂P) = ‖x‖ := (norm_eq_integral_abs_rep μ x U hx).symm
  have hg : (∫ z, excess t |U z.2| (Y z) ∂Pr) = midpointGain t x y := by
    rw [integral_measure_diagram hq hst (fun z => excess t |U z.2| (Y z))
      (fun ω => excess t |U ω| (V ω))
      (by unfold excess; exact (((hYm.abs.const_mul t).sub ((hUm.comp measurable_snd).abs)).max measurable_const))
      (by unfold excess; exact ((hVm.abs.const_mul t).sub hUm.abs).max measurable_const)
      (fun z => by rw [heU z, heY z])]
    exact (midpointGain_eq_integral_excess P x.val y.val U V hx hy t ht).symm
  change A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) * (∫ z, |Y z| ∂Pr) -
    D * (∫ old, |U old| ∂P) ≤ ∫ z, excess t |U z.2| (Y z) ∂Pr at ha
  rw [hnY, hnU, hg] at ha
  exact ha

end FiniteAffine
end FiniteHead
end IndependentProducts

end

end OAI
