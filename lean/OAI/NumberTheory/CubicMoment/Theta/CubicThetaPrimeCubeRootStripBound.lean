import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAutomorphicL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! A literal cusp strip has at most one representative in each orbit of
any subgroup of the principal group. Its mass is bounded by fundamental-domain
mass, also for the cubic-root cover. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace CubicFirstMoment

lemma cubicThetaInjective_subgroup_disjoint (K : Subgroup cubicThetaPrincipalGroup)
    {S : Set CubicThetaPoint} (hS : InjOn cubicThetaQuotientMap S) :
    Pairwise (fun g h : K => Disjoint (g • S) (h • S)) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  change g.val • a=x at hga
  change h.val • b=x at hgb
  have he : (h.val⁻¹*g.val) • a=b := by
    rw [mul_smul]
    rw [hga,←hgb]
    exact inv_smul_smul h.val b
  have hq : cubicThetaQuotientMap b=cubicThetaQuotientMap a :=
    cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mpr ⟨h.val⁻¹*g.val,he⟩
  have hab : b=a := hS hb ha hq
  have hone := cubicThetaPrincipal_fixed_eq_one (h.val⁻¹*g.val) a (he.trans hab)
  exact hgh (Subtype.ext (inv_mul_eq_one.mp hone).symm)

lemma cubicThetaInjective_subgroup_lintegral_le (K : Subgroup cubicThetaPrincipalGroup)
    {D S : Set CubicThetaPoint} (hD : IsFundamentalDomain K D cubicThetaPointMeasure)
    (hDm : MeasurableSet D) (hSm : MeasurableSet S) (hS : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaPoint → ℝ≥0∞) (hi : ∀ (g : K) x, f (g • x)=f x) :
    (∫⁻ x in S,f x ∂cubicThetaPointMeasure)≤∫⁻ x in D,f x ∂cubicThetaPointMeasure := by
  have hm (g : K) : MeasurableSet (g • S ∩ D) :=
    ((measurableEmbedding_const_smul g).measurableSet_image' hSm).inter hDm
  have hd : Pairwise (fun g h : K => Disjoint (g • S ∩ D) (h • S ∩ D)) := by
    intro g h hgh
    exact (cubicThetaInjective_subgroup_disjoint K hS hgh).mono inter_subset_left inter_subset_left
  rw [hD.setLIntegral_eq_tsum' f S]
  simp_rw [hi]
  rw [←lintegral_iUnion hm hd]
  apply lintegral_mono_set
  exact iUnion_subset fun _ => inter_subset_right

lemma cubicThetaPrimeCubeRoot_strip_lintegral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) :
    (∫⁻ x in cubicThetaCuspStrip 2,‖(‖F.val x‖^2:ℝ)‖ₑ ∂cubicThetaPointMeasure)≤
      ∫⁻ x in cubicThetaPrimeCubeRootCoverDomain hp,‖(‖F.val x‖^2:ℝ)‖ₑ ∂cubicThetaPointMeasure := by
  apply cubicThetaInjective_subgroup_lintegral_le (cubicThetaPrimeCubeRootCoverGroup hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (cubicThetaPrimeCubeRootCoverDomain_measurable hp) (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))
  intro g x
  rw [cubicThetaPrimeCubeRootSection_norm_invariant hp F g x]

lemma cubicThetaPrimeCubeRoot_strip_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    MemLp F.val.val 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  refine ⟨(F.val.val.continuous.norm.pow 2).aestronglyMeasurable,?_⟩
  have hf := (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mp F.property
  exact lt_of_le_of_lt (cubicThetaPrimeCubeRoot_strip_lintegral_le hp F.val) hf.hasFiniteIntegral

end CubicFirstMoment

end

end OAI
