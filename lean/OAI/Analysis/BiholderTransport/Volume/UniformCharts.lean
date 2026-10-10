import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Charts
import OAI.Analysis.BiholderTransport.Volume.ChartJacobianBounds

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module Metric
open scoped Topology ContDiff BigOperators NNReal

namespace WeakMTWTransport
section UniformCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_volume_charts :
    ∃ C : ℝ≥0, 0<C ∧ ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ x : M,
      ∃ a : M, ∃ U : Set M, IsOpen U ∧ x∈U ∧
        U⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) U ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a).symm
          ((extChartAt 𝓘(ℝ,Model n) a) '' U) ∧
        ∀ z∈U, l≤chartJacobian (n := n) a z ∧ chartJacobian (n := n) a z≤u := by
  classical
  have H (x : M) : ∃ C D : ℝ≥0, ∃ l u : ℝ, 0<l ∧ 0<u ∧
      ∃ U : Set M, IsOpen U ∧ x∈U ∧ U⊆(extChartAt 𝓘(ℝ,Model n) x).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) x) U ∧
        LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) x).symm
          ((extChartAt 𝓘(ℝ,Model n) x) '' U) ∧
        ∀ z∈U, l≤chartJacobian (n := n) x z ∧ chartJacobian (n := n) x z≤u := by
    obtain ⟨C,D,r,hr,hUs,hd,hdi⟩ := exists_bilipschitz_chart (n := n) x
    let U := ball x r
    have hUo : IsOpen U := isOpen_ball
    have hxU : x∈U := mem_ball_self hr
    obtain ⟨l,u,hl,hu,hnear⟩ := eventually_chartJacobian_bounds (n := n) x
    obtain ⟨V,hVs,hVo,hxV⟩ := _root_.mem_nhds_iff.mp hnear
    exact ⟨C,D,l,u,hl,hu,U∩V,hUo.inter hVo,⟨hxU,hxV⟩,
      inter_subset_left.trans hUs,hd.mono inter_subset_left,
      hdi.mono (image_mono inter_subset_left),fun z hz => hVs hz.2⟩
  choose C D l u hl hu U hUo hxU hUs hd hdi hj using H
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hUo
    (show univ⊆⋃ x, U x from fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
  let C0 : ℝ≥0 := 1+∑ a∈s, (C a+D a)
  let R : ℝ := 1+∑ a∈s, (l a)⁻¹
  let u0 : ℝ := 1+∑ a∈s, u a
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  have hR : 0<R := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (inv_pos.mpr (hl a)).le)
    dsimp [R]
    linarith
  have hu0 : 0<u0 := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (hu a).le)
    dsimp [u0]
    linarith
  refine ⟨C0,hC0,R⁻¹,u0,inv_pos.mpr hR,hu0,?_⟩
  intro x
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hCD : C a+D a≤C0 := by
    have h := Finset.single_le_sum (f := fun a => C a+D a) (fun _ _ => zero_le) ha
    exact h.trans (le_add_of_nonneg_left (by positivity))
  have hCa : C a≤C0 := (le_add_of_nonneg_right (zero_le)).trans hCD
  have hDa : D a≤C0 := (le_add_of_nonneg_left (zero_le)).trans hCD
  have hla : (l a)⁻¹≤R := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (inv_pos.mpr (hl b)).le) ha
    dsimp [R]
    linarith
  have hlower : R⁻¹≤l a := by
    have h := (inv_le_inv₀ hR (inv_pos.mpr (hl a))).mpr hla
    simpa only [inv_inv] using h
  have hua : u a≤u0 := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (hu b).le) ha
    dsimp [u0]
    linarith
  exact ⟨a,U a,hUo a,hxa,hUs a,(hd a).weaken hCa,(hdi a).weaken hDa,
    fun z hz => ⟨hlower.trans (hj a z hz).1,((hj a z hz).2).trans hua⟩⟩

end UniformCharts
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

lemma scalar_intrinsic_jacobian_bounds {d j D a b ell u c C : ℝ}
    (hd : 0≤d) (hjD : 0≤j*D) (hell : 0≤ell) (hc : 0<c) (hC : 0<C)
    (ha : c≤a ∧ a≤C) (hb : c≤b ∧ b≤C) (hl : ell≤d) (hu : d≤u)
    (heq : d*a=b*j*D) : ell*c/C≤j*D ∧ j*D≤u*C/c := by
  have ha0 : 0≤a := hc.le.trans ha.1
  have hu0 : 0≤u := hd.trans hu
  have hlow : ell*c≤d*a := by
    calc
      ell*c ≤ ell*a := mul_le_mul_of_nonneg_left ha.1 hell
      _ ≤ d*a := mul_le_mul_of_nonneg_right hl ha0
  have hhigh : d*a≤u*C := mul_le_mul hu ha.2 ha0 hu0
  constructor
  · apply (div_le_iff₀ hC).mpr
    calc
      ell*c ≤ d*a := hlow
      _ = b*(j*D) := by nlinarith [heq]
      _ ≤ C*(j*D) := mul_le_mul_of_nonneg_right hb.2 hjD
      _ = j*D*C := by ring
  · apply (le_div_iff₀ hc).mpr
    calc
      j*D*c = c*(j*D) := by ring
      _ ≤ b*(j*D) := mul_le_mul_of_nonneg_right hb.1 hjD
      _ = d*a := by nlinarith [heq]
      _ ≤ u*C := hhigh

end WeakMTWTransport
end
end
end

end OAI
