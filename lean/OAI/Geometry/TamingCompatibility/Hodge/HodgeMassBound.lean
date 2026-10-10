import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeMixing
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShellLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeQuantitative

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel unitT2

include hE D hD in
lemma same_resolvent_current_mass_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ], ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize g μ‖^2 ≤ (C*M+B)/r^2 := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_current_point_bound A J α hs ht E hE D hD g
  refine ⟨16*C,B,mul_nonneg (by norm_num) hC,hB,?_⟩
  intro μ _ M hM hgrowth r hr hr1 S
  have hb : Continuous (fun v : MetricUnit g => v.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  let P : X → MetricUnit g → ℝ := fun x v => ((1+dist x v.val.proj/r)⁻¹)^6
  have hm (x : X) : Measurable (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hp (x : X) : Continuous (P x) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.add ((continuous_const.dist hb).div_const r)
    · intro v
      have h : 0 < 1+dist x v.val.proj/r := by positivity
      exact h.ne'
  have hi (x : X) : Integrable (P x) μ :=
    (hp x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint (x : X) : (∫ v, P x v ∂μ) ≤ 8*M*r^2 := by
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) (hm x) M hM (hgrowth x) hr
    have he (v : MetricUnit g) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist x v.val.proj))).toReal = P x v := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  have hcoef : 0 ≤ C/r^4+C/r^2 := by positivity
  have hinner (u : MetricUnit g) : ‖∫ v, S.innerKernel g u v ∂μ‖ ≤ (16*C*M+B)/r^2 := by
    calc
      _ ≤ ∫ v, |S.innerKernel g u v| ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ v, (C/r^4+C/r^2)*P u.val.proj v+B ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
          (((hi u.val.proj).const_mul _).add (integrable_const _))
          (Eventually.of_forall (hbound r hr S u))
      _ = (C/r^4+C/r^2)*(∫ v, P u.val.proj v ∂μ)+B := by
        rw [integral_add ((hi u.val.proj).const_mul _) (integrable_const _),
          integral_const_mul,integral_const,probReal_univ,one_smul]
      _ ≤ (C/r^4+C/r^2)*(8*M*r^2)+B :=
        add_le_add (mul_le_mul_of_nonneg_left (hint u.val.proj) hcoef) le_rfl
      _ = (8*C*M+8*C*M*r^2+B*r^2)/r^2 := by
        field_simp
      _ ≤ (16*C*M+B)/r^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg r)
        have hr2 : r^2 ≤ 1 := pow_le_one₀ hr.le hr1
        have h1 := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 8*C*M)
        have h2 := mul_le_mul_of_nonneg_left hr2 hB
        nlinarith
  have hout := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hinner)
  rw [probReal_univ,mul_one,← S.regularize_inner g μ μ,real_inner_self_eq_norm_sq,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hout
  exact hout

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel unitT2

include hE D hD in
lemma same_resolvent_current_mass_cross :
    let := geometricMetricSpace J α hs ht
    ∀ (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ], ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ∀ V : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪S.regularize g μ,V⟫| ≤ K*‖V‖ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  intro μ _ M hM hgrowth
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_current_mass_bound A J α hs ht E hE D hD g
  obtain ⟨L,hL,hcross⟩ := hodge_regularized_positive_current_cross A J α hs ht D hD
  have hCB : 0 ≤ C*M+B := add_nonneg (mul_nonneg hC hM) hB
  refine ⟨L*Real.sqrt (C*M+B),mul_nonneg hL (Real.sqrt_nonneg _),?_⟩
  intro r hr hr1 S V hV
  have hm := hbound μ M hM hgrowth r hr hr1 S
  have hm' : (r*‖S.regularize g μ‖)^2 ≤ C*M+B := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hm
    nlinarith
  have hsqrt : r*‖S.regularize g μ‖ ≤ Real.sqrt (C*M+B) := by
    have hh := Real.sq_sqrt hCB
    have hp := Real.sqrt_nonneg (C*M+B)
    nlinarith [norm_nonneg (S.regularize g μ)]
  calc
    _ ≤ L*r*‖S.regularize g μ‖*‖V‖ := hcross r hr hr1 S g μ V hV
    _ = L*(r*‖S.regularize g μ‖)*‖V‖ := by ring
    _ ≤ (L*Real.sqrt (C*M+B))*‖V‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hL) (norm_nonneg V)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
