import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthMomentKernel
import OAI.Geometry.TamingCompatibility.DifferentialForms.RationalKernelCompare
import OAI.Geometry.TamingCompatibility.DifferentialForms.EuclideanUnitPlanes

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
open RadialPotential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma transverse_sub (u v z w : V) :
    transverse u v (z-w) = transverse u v z - transverse u v w := by
  simp only [transverse,inner_sub_right,sub_smul]
  abel

lemma transverse_smul (u v z : V) (c : ℝ) :
    transverse u v (c • z) = c • transverse u v z := by
  simp only [transverse,real_inner_smul_right,smul_sub,smul_smul]

lemma norm_transverse_le (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖ ≤ ‖z‖ := by
  have hh := norm_transverse_sq u v z hu hv huv
  nlinarith [sq_nonneg ⟪u,z⟫,sq_nonneg ⟪v,z⟫,norm_nonneg (transverse u v z),norm_nonneg z]

lemma transverse_first (a b : V) (ha : a ≠ 0) (_hab : normalPart a b ≠ 0) :
    transverse (first a) (second a b) a = 0 := by
  have h1 := first_second_orthogonal ha b
  have hv : ⟪second a b,first a⟫ = 0 := (real_inner_comm _ _).trans h1
  conv_lhs => arg 3; rw [← first_reconstruct a]
  rw [transverse_smul]
  simp only [transverse,real_inner_self_eq_norm_sq,norm_first ha,one_pow,one_smul,hv,zero_smul,sub_self,smul_zero]

lemma transverse_second (a b : V) (ha : a ≠ 0) (hab : normalPart a b ≠ 0) :
    transverse (first a) (second a b) b = 0 := by
  have hu := norm_first ha
  have hv := norm_second hab
  have h1 := first_second_orthogonal ha b
  have h2 : ⟪second a b,first a⟫ = 0 := (real_inner_comm _ _).trans h1
  have he (c d : ℝ) : transverse (first a) (second a b) (c • first a + d • second a b) = 0 := by
    simp only [transverse,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      hu,hv,h1,h2,one_pow,mul_one,mul_zero,add_zero,zero_add,add_sub_cancel_left,sub_self]
  conv_lhs => arg 3; rw [reconstruct_second a b]
  exact he _ _

lemma graph_projection_norm (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (z a : V) (ha : a ≠ 0) :
    let G := hermitianGraph K
    let c := ⟪G z,G a⟫/‖G a‖^2
    let d := ⟪G z,G (K a)⟫/‖G a‖^2
    ‖G (z-c • a-d • K a)‖ ≤ Real.sqrt (hermitianDefect K z a)/‖G a‖ := by
  dsimp only
  let G := hermitianGraph K
  have han : 0 < ‖G a‖ := lt_of_lt_of_le (norm_pos_iff.mpr ha) (hermitianGraph_norm_ge K a)
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK a
  have hr : ‖G (z-(⟪G z,G a⟫/‖G a‖^2) • a-(⟪G z,G (K a)⟫/‖G a‖^2) • K a)‖^2 =
      hermitianDefect K z a/‖G a‖^2 := by
    simp only [map_sub,map_smul]
    rw [norm_sub_sq_real,norm_sub_sq_real,inner_sub_left]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left,real_inner_smul_right]
    rw [show ⟪G a,G (K a)⟫ = 0 from ho,show ‖G (K a)‖ = ‖G a‖ from hn]
    change _ = (‖G z‖^2*‖G a‖^2-⟪G z,G a⟫^2-⟪G z,G (K a)⟫^2)/‖G a‖^2
    field_simp
    ring
  have hs := Real.sq_sqrt (hermitianDefect_nonneg K hK z a)
  have he : (Real.sqrt (hermitianDefect K z a)/‖G a‖)^2 = hermitianDefect K z a/‖G a‖^2 := by
    rw [div_pow,hs]
  have hp : 0 ≤ Real.sqrt (hermitianDefect K z a)/‖G a‖ := by positivity
  nlinarith [norm_nonneg (G (z-(⟪G z,G a⟫/‖G a‖^2) • a-(⟪G z,G (K a)⟫/‖G a‖^2) • K a))]

lemma graph_coefficient_bound (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (z a : V) (ha : a ≠ 0) :
    |⟪hermitianGraph K z,hermitianGraph K (K a)⟫/‖hermitianGraph K a‖^2| * ‖a‖ ≤
      ‖hermitianGraph K z‖ := by
  let G := hermitianGraph K
  have han : 0 < ‖G a‖ := lt_of_lt_of_le (norm_pos_iff.mpr ha) (hermitianGraph_norm_ge K a)
  have hh := abs_real_inner_le_norm (G z) (G (K a))
  rw [(hermitianGraph_complex_pair K hK a).2] at hh
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖hermitianGraph K a‖)]
  have hc : |⟪G z,G (K a)⟫|/‖G a‖^2 ≤ ‖G z‖/‖G a‖ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos han) han).mpr
    nlinarith
  calc
    _ ≤ (‖G z‖/‖G a‖)*‖a‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg a)
    _ ≤ (‖G z‖/‖G a‖)*‖G a‖ := mul_le_mul_of_nonneg_left (hermitianGraph_norm_ge K a) (by positivity)
    _ = _ := div_mul_cancel₀ _ han.ne'

lemma transverse_graph_bound (K L : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (hL : ∀ v, L (L v) = -v) (z a : V) (ha : a ≠ 0) :
    ‖transverse (first a) (second a (L a)) z‖ ≤
      Real.sqrt (hermitianDefect K z a)/‖hermitianGraph K a‖ +
        ‖hermitianGraph K z‖*‖K-L‖ := by
  let G := hermitianGraph K
  let c := ⟪G z,G a⟫/‖G a‖^2
  let d := ⟪G z,G (K a)⟫/‖G a‖^2
  let R := z-c • a-d • K a
  let u := first a
  let v := second a (L a)
  have hab := normalPart_complex_ne_zero L hL ha
  have hu : ‖u‖ = 1 := norm_first ha
  have hv : ‖v‖ = 1 := norm_second hab
  have huv : ⟪u,v⟫ = 0 := first_second_orthogonal ha _
  have hta : transverse u v a = 0 := transverse_first a (L a) ha hab
  have htb : transverse u v (L a) = 0 := transverse_second a (L a) ha hab
  have hz : transverse u v z = transverse u v R + d • transverse u v ((K-L) a) := by
    simp only [R,transverse_sub,transverse_smul,sub_apply,
      hta,htb,sub_zero,smul_zero]
    abel
  calc
    _ ≤ ‖transverse u v R‖+‖d • transverse u v ((K-L) a)‖ := by rw [hz]; exact norm_add_le _ _
    _ ≤ ‖R‖+|d| * ‖(K-L) a‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (norm_transverse_le u v R hu hv huv)
        (mul_le_mul_of_nonneg_left (norm_transverse_le u v _ hu hv huv) (abs_nonneg d))
    _ ≤ ‖G R‖+|d| * (‖K-L‖*‖a‖) := add_le_add (hermitianGraph_norm_ge K R)
      (mul_le_mul_of_nonneg_left ((K-L).le_opNorm a) (abs_nonneg d))
    _ ≤ _ := by
      have hh := graph_projection_norm K hK z a ha
      have hc := mul_le_mul_of_nonneg_right (graph_coefficient_bound K hK z a ha) (norm_nonneg (K-L))
      change ‖G R‖ ≤ _ at hh
      change (|d| * ‖a‖)*‖K-L‖ ≤ _ at hc
      nlinarith
end TamingCompatibility.PlaneVariation

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [CompactSpace X] [T2Space X] in
lemma unitChartFirst_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartFirst J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  exact (first_continuousAt (unitChartVector_ne_zero J α hs ht p u
    (unitChart_mem J α hs ht p hKT hu).1)).comp_continuousWithinAt
      ((unitChartVector_continuousOn J α hs ht p hKT) u hu)

omit [CompactSpace X] [T2Space X] in
lemma unitChartSecond_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartSecond J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  have ha := unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1
  have hab := normalPart_complex_ne_zero _ (coordinateJ_square J p
    (hKT (unitChart_mem J α hs ht p hKT hu).2)) ha
  apply ContinuousAt.comp_continuousWithinAt
    (f := fun v => (unitChartVector J α hs ht p v,unitChartJVector J α hs ht p v))
    (second_continuousAt ha hab)
  exact     (((unitChartVector_continuousOn J α hs ht p hKT) u hu).prodMk
      ((unitChartJVector_continuousOn J α hs ht p hKT) u hu))

def unitTransverse (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  transverse (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u)
    (unitChartBase J α hs ht p u-b)

omit [CompactSpace X] [T2Space X] in
lemma unitTransverse_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitTransverse J α hs ht p b) (unitChartDomain J α hs ht p K) := by
  let f := unitChartFirst J α hs ht p
  let g := unitChartSecond J α hs ht p
  let z := fun u => unitChartBase J α hs ht p u-b
  let S := unitChartDomain J α hs ht p K
  have hc : ContinuousOn z S := (unitChartBase_continuousOn J α hs ht p hKT).sub continuousOn_const
  have hf : ContinuousOn f S := unitChartFirst_continuousOn J α hs ht p hKT
  have hg : ContinuousOn g S := unitChartSecond_continuousOn J α hs ht p hKT
  have hi : ContinuousOn (fun u => inner ℝ (f u) (z u)) S := hf.inner hc
  have hj : ContinuousOn (fun u => inner ℝ (g u) (z u)) S := hg.inner hc
  have hif : ContinuousOn (fun u => (inner ℝ (f u) (z u)) • f u) S := hi.smul hf
  have hjg : ContinuousOn (fun u => (inner ℝ (g u) (z u)) • g u) S := hj.smul hg
  exact (hc.sub hif).sub hjg

lemma unitChartVector_lower (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ unitChartDomain J α hs ht p K,
      m ≤ ‖unitChartVector J α hs ht p u‖ := by
  have hS := (unitChartDomain_closed J α hs ht p hK hKT).isCompact
  have hc := (unitChartVector_continuousOn J α hs ht p hKT).norm
  have hp : ∀ u ∈ unitChartDomain J α hs ht p K, 0 < ‖unitChartVector J α hs ht p u‖ :=
    fun u hu => norm_pos_iff.mpr (unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1)
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn (hc.inv₀ (fun u hu => ne_of_gt (hp u hu)))
  refine ⟨(max M 1)⁻¹,by positivity,fun u hu => ?_⟩
  have hm := hM u hu
  change ‖‖unitChartVector J α hs ht p u‖⁻¹‖ ≤ M at hm
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hp u hu))] at hm
  exact (inv_le_comm₀ (hp u hu) (lt_of_lt_of_le zero_lt_one (le_max_right M 1))).mp
    (hm.trans (le_max_left _ _))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
