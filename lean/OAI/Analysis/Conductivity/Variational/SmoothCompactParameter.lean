import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

section CompactParameter
variable {E Q P G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace P] [SecondCountableTopology P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure P} [IsFiniteMeasure μ]

omit [CompleteSpace G] in
lemma hasFDerivAt_compact_parameter {F : E × P → G} {D : E × P → E →L[ℝ] G}
    (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ x p, HasFDerivAt (fun y => F (y,p)) (D (x,p)) x) (x : E) :
    HasFDerivAt (fun y => ∫ p, F (y,p) ∂μ) (∫ p, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_univ : IsCompact (univ : Set P))).exists_bound_of_continuousOn
    hD.continuousOn
  have hFs (y : E) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDs (y : E) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (s := closedBall x 1) (bound := fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hFs y).aestronglyMeasurable)
    ((hFs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDs x).aestronglyMeasurable _ (integrable_const _)
  · exact Eventually.of_forall (fun p y _ => hd y p)
  · exact Eventually.of_forall (fun p y hy => hC (y,p) ⟨hy,mem_univ p⟩)

omit [CompleteSpace G] in
lemma hasDerivAt_compact_parameter {F D : ℝ × P → G}
    (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ x p, HasDerivAt (fun y => F (y,p)) (D (x,p)) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ p, F (y,p) ∂μ) (∫ p, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_univ : IsCompact (univ : Set P))).exists_bound_of_continuousOn
    hD.continuousOn
  have hFs (y : ℝ) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDs (y : ℝ) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=fun y p => F (y,p)) (F':=fun y p => D (y,p))
    (s:=closedBall x 1) (bound:=fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hFs y).aestronglyMeasurable)
    ((hFs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDs x).aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall (fun p y hy => hC (y,p) ⟨hy,mem_univ p⟩)
  · exact Eventually.of_forall (fun p y _ => hd y p)

lemma contDiff_compact_parameter_nat (n : ℕ) {F : E × Q → G}
    (hF : ContDiff ℝ n F) {r : P → Q} (hr : Continuous r) :
    ContDiff ℝ n (fun x => ∫ p, F (x,r p) ∂μ) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    have hFC : Continuous (fun z : E × P => F (z.1,r z.2)) :=
      hF.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ:=μ)
        (f:=fun x p => F (x,r p)) hFC (isCompact_univ : IsCompact (univ : Set P))
  | succ n ih =>
    let D : E × Q → E →L[ℝ] G := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E Q)
    have hD : ContDiff ℝ n D :=
      (hF.fderiv_right (by norm_cast)).clm_comp contDiff_const
    have hd : ∀ x p, HasFDerivAt (fun y => F (y,r p)) (D (x,r p)) x := by
      intro x p
      exact ((hF.differentiable (by norm_cast)).differentiableAt.hasFDerivAt
        (x:=(x,r p))).comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (r p) x))
    rw [Nat.cast_add,Nat.cast_one]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ p, D (x,r p) ∂μ,ih hD,?_⟩
    intro x
    apply hasFDerivAt_compact_parameter (F:=fun z : E × P => F (z.1,r z.2))
      (D:=fun z : E × P => D (z.1,r z.2))
    · exact hF.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    · exact hD.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
    · exact hd

lemma contDiff_compact_parameter {F : E × Q → G}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) {r : P → Q} (hr : Continuous r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∫ p, F (x,r p) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_compact_parameter_nat n (contDiff_infty.mp hF n) hr

end CompactParameter
end ScalarConductivity

end
end

end OAI
