import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HarmonicSeminormBound
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAntiRHSBound

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in
lemma smoothAntiProjection_cube_norm (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    ‖smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val‖ ≤
      ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖ := by
  change ‖smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a)‖ ≤ _
  rw [preAntiProjection_smooth]
  calc
    _ ≤ ‖smoothL2 A J α hs ht true a‖ := l2AntiProjection_norm A J α hs ht _
    _ = ‖hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a))‖ := by
      rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr]
    _ ≤ _ := hodgeRegularization_norm_le A J α hs ht r _

omit [T2Space X] in
lemma smoothAntiProjection_cube_dual (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) (v : antiEnergy A J α hs ht) :
    |⟪smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val,
      energyInclusion A J α hs ht v⟫| ≤
      (‖energyInclusion A J α hs ht‖ *
        ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖)*‖v‖ := by
  calc
    _ ≤ ‖smoothL2 A J α hs ht true (smoothAntiProjection A J α hs ht a).val‖ *
        ‖energyInclusion A J α hs ht v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖ *
        (‖energyInclusion A J α hs ht‖*‖v‖) :=
      mul_le_mul (smoothAntiProjection_cube_norm A J α hs ht r hr a)
        ((energyInclusion A J α hs ht).le_opNorm v) (norm_nonneg _ ) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma hodge_lift_local_estimate
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
    (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
    (hwq : coordinateWeight A p q ≠ 0) :
    ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
        ∀ (a : PreL2 A J α hs ht true) (x : Space), x ∈ O →
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht
            (Gs (smoothAntiProjection A J α hs ht a)).val.val))
            (extChartAt Model p.val).symm x‖ ≤
              C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,B,hB,hL⟩ :=
    hodgeRegularization_uniform_local_H3 A J α hs ht D hD p q hq hwq
  obtain ⟨ρ,_,hρ,O,hO,hqO,hOD,C,hC,hest⟩ :=
    exists_local_ddstar_estimate_on A J α hs ht (fun p => (D p).toData) hD
      p τ U hU hUD hτ q hqU
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_antiRHS_bound A J α hs ht D hD p τ χ U hχ B hB hL ρ hρ
  let F := rawRHSSeminormMap A J α hs ht (fun p => (D p).toData) hD p τ ρ
  obtain ⟨B₂,hB₂,h₂⟩ := harmonic_seminorm_bound A J α hs ht (fun p => (D p).toData) hD F
  let E := C₀*‖energyInclusion A J α hs ht‖
  have hE : 0 ≤ E := mul_nonneg hC₀.le (norm_nonneg (energyInclusion A J α hs ht))
  refine ⟨O,hO,hqO,hOD,C*(E+B₁+B₂),mul_nonneg hC (by positivity),fun r hr hr1 a x hx => ?_⟩
  let f := smoothAntiProjection A J α hs ht a
  let N := ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖
  have hN : 0 ≤ N := norm_nonneg _
  have ht1 : 1 ≤ (r⁻¹)^3 := one_le_pow₀ ((one_le_inv₀ hr).mpr hr1)
  have he : ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ E*N := by
    exact (hdual f (‖energyInclusion A J α hs ht‖*N) (mul_nonneg (norm_nonneg (energyInclusion A J α hs ht)) hN)
      (smoothAntiProjection_cube_dual A J α hs ht r hr a)).trans_eq (by dsimp [E]; ring)
  have hf : ‖F f‖ ≤ B₁*(r⁻¹)^3*N := h₁ r hr hr1 a
  have hh : ‖F (H f)‖ ≤ B₂*N := (h₂ f (H f) (hH f)).trans
    (mul_le_mul_of_nonneg_left (smoothAntiProjection_cube_norm A J α hs ht r hr a) hB₂)
  have hdiff : ‖F (f-H f)‖ ≤ B₁*(r⁻¹)^3*N+B₂*N := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add hf hh)
  have hb := hest (f-H f) (Gs f) (hweak f) x hx
  change _ ≤ C*(‖antiToEnergy A J α hs ht (Gs f)‖+‖F (f-H f)‖) at hb
  calc
    _ ≤ _ := hb
    _ ≤ C*(E*N+(B₁*(r⁻¹)^3*N+B₂*N)) := mul_le_mul_of_nonneg_left (add_le_add he hdiff) hC
    _ ≤ C*((E+B₁+B₂)*(r⁻¹)^3*N) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have he' := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hE hN)
      have hh' := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hB₂ hN)
      nlinarith
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldVolume Bundle Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def chartDirectionFactor (J : AlmostComplexStructure X) (p : X) (v : TangentBundle Model X) : ℝ :=
  ‖((trivializationAt Space (TangentSpace Model) p) v).2‖ *
    ‖((trivializationAt Space (TangentSpace Model) p)
      (⟨v.proj,J.endomorphism v.proj v.2⟩ : TangentBundle Model X)).2‖

lemma chartDirectionFactor_nonneg (J : AlmostComplexStructure X) (p : X)
    (v : TangentBundle Model X) : 0 ≤ chartDirectionFactor J p v := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma chartDirectionFactor_continuousAt (J : AlmostComplexStructure X) (p : X)
    (v : TangentBundle Model X) (hv : v.proj ∈ (extChartAt Model p).source) :
    ContinuousAt (chartDirectionFactor J p) v := by
  let e := trivializationAt Space (TangentSpace Model) p
  have hb : v.proj ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hv
  have h₁ := (e.continuousAt (e.mem_source.mpr hb)).snd.norm
  have hj : (⟨v.proj,J.endomorphism v.proj v.2⟩ : TangentBundle Model X) ∈ e.source :=
    e.mem_source.mpr hb
  have h₂ := ((e.continuousAt hj).comp (f := fun w : TangentBundle Model X =>
      (⟨w.proj,J.endomorphism w.proj w.2⟩ : TangentBundle Model X))
    (show ContinuousAt (fun w : TangentBundle Model X =>
      (⟨w.proj,J.endomorphism w.proj w.2⟩ : TangentBundle Model X)) v from
      J.smooth.continuous.continuousAt)).snd.norm
  exact h₁.mul h₂

lemma eval_le_chartDirectionFactor (J : AlmostComplexStructure X) (p : X)
    (β : TwoForm X) (v : TangentBundle Model X) (hv : v.proj ∈ (extChartAt Model p).source) :
    ‖eval β v.proj v.2 (J.endomorphism v.proj v.2)‖ ≤
      ‖ManifoldForms.pullback β (extChartAt Model p).symm ((extChartAt Model p) v.proj)‖ *
        chartDirectionFactor J p v := by
  let e := extChartAt Model p
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : v.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hv
  have hp : ManifoldForms.pullback β e.symm (e v.proj) =
      (β v.proj).compContinuousLinearMap (t.symmL ℝ v.proj) := by
    unfold ManifoldForms.pullback
    rw [inverseChart_derivative p (e.map_source hv),e.left_inv hv]
  let u := t.continuousLinearMapAt ℝ v.proj v.2
  let w := t.continuousLinearMapAt ℝ v.proj (J.endomorphism v.proj v.2)
  have he : (ManifoldForms.pullback β e.symm (e v.proj)) ![u,w] =
      eval β v.proj v.2 (J.endomorphism v.proj v.2) := by
    rw [hp]
    change (β v.proj) (fun i => t.symmL ℝ v.proj (![u,w] i)) = _
    have hu : t.symmL ℝ v.proj u = v.2 := t.symmL_continuousLinearMapAt hb v.2
    have hw : t.symmL ℝ v.proj w = J.endomorphism v.proj v.2 := t.symmL_continuousLinearMapAt hb _
    have heq : (fun i => t.symmL ℝ v.proj (![u,w] i)) = ![v.2,J.endomorphism v.proj v.2] := by
      funext i
      fin_cases i
      · exact hu
      · exact hw
    rw [heq]
    rfl
  rw [← he]
  have h := (ManifoldForms.pullback β e.symm (e v.proj)).le_opNorm ![u,w]
  simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,chartDirectionFactor,
    u,w,Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb] using h

end TamingCompatibility

end
end

end
end

end OAI
