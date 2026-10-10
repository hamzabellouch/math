import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothLaplacian

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraphResolvent_raw_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ u : hodgeEnergy A J α hs ht, MemSobolevLoc V 5
        (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) u)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU 1 zero_lt_one
  obtain ⟨V,hV,hqV,hVW,hVgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hW (hWU.trans hUD) (fun z hz => hτ z (hWU hz)) q hqW 1 zero_lt_one
  refine ⟨τ,V,hV,hqV,hVW.trans (hWU.trans hUD),fun z hz => hτ z (hWU (hVW hz)),?_⟩
  intro u
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) U
  have h₂ : MemSobolevLoc W (3:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
    simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply] using hWgain 1 u (by simpa only [Nat.cast_one] using h₁)
  have h₃ := hVgain 3 (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)
    (by simpa only [Nat.cast_ofNat] using h₂)
  change MemSobolevLoc V 5 (hodgeRawDistribution A J α hs ht D hD p τ
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)))
  simpa only [Nat.cast_ofNat,show (3:ℝ)+2=5 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply] using h₃

lemma exists_hodgeGraphResolvent_lift (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ L : hodgeEnergy A J α hs ht →L[ℝ] H Space (C 6) 5,
        ∀ u, toDistribution Space (C 6) 5 (L u) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            ((hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) u)) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeGraphResolvent_raw_H5 A J α hs ht D hD p q hq hwq
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let F : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,C 6) :=
    ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
      ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2))
  have hF : ∀ u, MemSobolev 5 2 (F u) := fun u => hreg u χ hχc hχV
  refine ⟨τ,χ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_,
    realSobolevLift 5 F hF,realSobolevLift_spec 5 F hF⟩
  intro z hz
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeEnergy_prod_norm_sq (u : hodgeEnergy A J α hs ht) :
    ‖u‖^2 = ‖hodgeInclusion A J α hs ht u‖^2 + ‖hodgeWeakDerivative A J α hs ht u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

lemma hodgeEnergy_prod_norm_le (u : hodgeEnergy A J α hs ht) :
    ‖u‖ ≤ ‖hodgeInclusion A J α hs ht u‖ + ‖hodgeWeakDerivative A J α hs ht u‖ := by
  have h := hodgeEnergy_prod_norm_sq A J α hs ht u
  nlinarith [norm_nonneg u,norm_nonneg (hodgeInclusion A J α hs ht u),
    norm_nonneg (hodgeWeakDerivative A J α hs ht u),
    mul_nonneg (norm_nonneg (hodgeInclusion A J α hs ht u))
      (norm_nonneg (hodgeWeakDerivative A J α hs ht u))]

lemma hodgeWeakSolution_derivative_bound (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ ≤ r⁻¹*‖f‖ := by
  let u := hodgeWeakSolution A J α hs ht r hr f
  have hi : hodgeInclusion A J α hs ht u = hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have he := hodgeWeakSolution_identity A J α hs ht r hr f u
  rw [hi,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
  have hb := hodgeResolvent_norm_le A J α hs ht r f
  have hc := real_inner_le_norm f (hodgeResolvent A J α hs ht r f)
  have hsq : (r*‖hodgeWeakDerivative A J α hs ht u‖)^2 ≤ ‖f‖^2 := by
    nlinarith [sq_nonneg ‖hodgeResolvent A J α hs ht r f‖,
      mul_le_mul_of_nonneg_left hb (norm_nonneg f)]
  have hm : r*‖hodgeWeakDerivative A J α hs ht u‖ ≤ ‖f‖ := by
    nlinarith [norm_nonneg f,mul_nonneg hr.le (norm_nonneg (hodgeWeakDerivative A J α hs ht u))]
  calc
    ‖hodgeWeakDerivative A J α hs ht u‖ = r⁻¹*(r*‖hodgeWeakDerivative A J α hs ht u‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    _ ≤ r⁻¹*‖f‖ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hr.le)

lemma hodgeWeakSolution_graph_bound (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakSolution A J α hs ht r hr f‖ ≤ (1+r⁻¹)*‖f‖ := by
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  calc
    _ ≤ ‖hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ +
        ‖hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ :=
      hodgeEnergy_prod_norm_le A J α hs ht _
    _ ≤ ‖f‖+r⁻¹*‖f‖ := by
      rw [hi]
      exact add_le_add (hodgeResolvent_norm_le A J α hs ht r f)
        (hodgeWeakSolution_derivative_bound A J α hs ht r hr f)
    _ = _ := by ring

lemma hodgeWeakSolution_graph_small_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakSolution A J α hs ht r hr f‖ ≤ 2*r⁻¹*‖f‖ := by
  have hi : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  exact (hodgeWeakSolution_graph_bound A J α hs ht r hr f).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f))
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
