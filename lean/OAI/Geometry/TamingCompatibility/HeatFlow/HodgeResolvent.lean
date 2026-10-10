import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeTestPairing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeShiftedRegularity

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeScaledDerivative (r : ℝ) : hodgeEnergy A J α hs ht →L[ℝ] HodgeDerivativePair A J α hs ht :=
  r • hodgeWeakDerivative A J α hs ht

@[simp] lemma hodgeScaledDerivative_apply (r : ℝ) (u : hodgeEnergy A J α hs ht) :
    hodgeScaledDerivative A J α hs ht r u = r • hodgeWeakDerivative A J α hs ht u := rfl

lemma hodgeEnergy_coercive (r : ℝ) (hr : 0 < r) : IsCoercive
    (Variational.energy (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)) := by
  refine ⟨min 1 (r^2),lt_min zero_lt_one (sq_pos_of_pos hr),fun u => ?_⟩
  rw [Variational.energy_apply,hodgeScaledDerivative_apply,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have hh := WithLp.prod_norm_sq_eq_of_L2 u.val
  change min 1 (r^2)*‖u.val‖*‖u.val‖ ≤ ‖u.val.fst‖^2 + r*(r*‖u.val.snd‖^2)
  have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 (r^2)) (sq_nonneg ‖u.val.fst‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 (r^2)) (sq_nonneg ‖u.val.snd‖)
  calc
    min 1 (r^2)*‖u.val‖*‖u.val‖ = min 1 (r^2)*‖u.val‖^2 := by ring
    _ = min 1 (r^2)*(‖u.val.fst‖^2+‖u.val.snd‖^2) := by rw [hh]
    _ ≤ ‖u.val.fst‖^2+r*(r*‖u.val.snd‖^2) := by nlinarith only [h1,h2]

def hodgeResolvent (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  if hr : 0 < r then
    Variational.resolvent (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)
      (hodgeEnergy_coercive A J α hs ht r hr)
  else 1

def hodgeWeakSolution (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  Variational.weakSolution (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)
    (hodgeEnergy_coercive A J α hs ht r hr)

lemma hodgeResolvent_eq (r : ℝ) (hr : 0 < r) : hodgeResolvent A J α hs ht r =
    (hodgeInclusion A J α hs ht).comp (hodgeWeakSolution A J α hs ht r hr) := by
  simp only [hodgeResolvent,dite_eq_left hr,Variational.resolvent,hodgeWeakSolution]

lemma hodgeWeakSolution_identity_raw (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (v : hodgeEnergy A J α hs ht) :
    Variational.energy (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true)
      (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht)
      (hodgeScaledDerivative A J α hs ht r) (hodgeWeakSolution A J α hs ht r hr f) v =
        ⟪f,hodgeInclusion A J α hs ht v⟫ := by
  exact Variational.weakSolution_identity _ _ _ f v

lemma hodgeWeakSolution_identity (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (v : hodgeEnergy A J α hs ht) :
    ⟪hodgeResolvent A J α hs ht r f,hodgeInclusion A J α hs ht v⟫ +
      r^2*⟪hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f),
        hodgeWeakDerivative A J α hs ht v⟫ = ⟪f,hodgeInclusion A J α hs ht v⟫ := by
  have h := hodgeWeakSolution_identity_raw A J α hs ht r hr f v
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply]
  simpa only [Variational.energy_apply,hodgeScaledDerivative_apply,
    real_inner_smul_left,real_inner_smul_right,pow_two,mul_assoc] using h

lemma hodgeResolvent_symmetric (r : ℝ) : (hodgeResolvent A J α hs ht r).toLinearMap.IsSymmetric := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_symmetric _ _ _
  · intro f g; rfl

lemma hodgeResolvent_nonnegative (r : ℝ) (f : L2 A J α hs ht true) :
    0 ≤ ⟪f,hodgeResolvent A J α hs ht r f⟫ := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_nonnegative _ _ _ f
  · exact real_inner_self_nonneg

lemma hodgeResolvent_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeResolvent A J α hs ht r f‖ ≤ ‖f‖ := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_norm_le _ _ _ f
  · exact le_rfl

def hodgeRegularization (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  hodgeResolvent A J α hs ht r ^ 3

lemma hodgeRegularization_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeRegularization A J α hs ht r f‖ ≤ ‖f‖ := by
  change ‖hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))‖ ≤ ‖f‖
  exact (hodgeResolvent_norm_le A J α hs ht r _).trans
    ((hodgeResolvent_norm_le A J α hs ht r _).trans (hodgeResolvent_norm_le A J α hs ht r f))
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_resolvent_distribution (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (r : ℝ) (hr : 0 < r) (f : hodgeEnergy A J α hs ht)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ
      (((r^2)⁻¹:ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f)))) =
    smulLeftCLM (C 6) χ (((r^2)⁻¹:ℂ) •
      smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
        (hodgeRawDistribution A J α hs ht D hD p τ f)) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  ext j
  let v := hodgeTest A J α hs ht D p (componentTest j φ)
    (full_componentTest_compact j φ hφ) ((full_componentTest_support j φ).trans (hφU.trans hUD))
  let u := hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f)
  have h := hodgeWeakSolution_identity A J α hs ht r hr (hodgeInclusion A J α hs ht f)
    (hodgeSmooth A J α hs ht v)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at h
  have he : ⟪hodgeWeakDerivative A J α hs ht u,
      hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ +
      (r^2)⁻¹*⟪hodgeInclusion A J α hs ht u,
        hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
      (r^2)⁻¹*⟪hodgeInclusion A J α hs ht f,
        hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ := by
    have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
    field_simp
    nlinarith only [h]
  simp only [fullShiftedSquare,_root_.add_apply,PiLp.add_apply,
    FunLike.coe_smul,smulLeftCLM_smul (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
    _root_.smul_apply,PiLp.smul_apply,smul_eq_mul]
  rw [hodge_raw_square_energy A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j]
  exact_mod_cast he
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
