import Mathlib
import OAI.Analysis.BiholderTransport.Volume.IntrinsicJacobian

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartJacobianBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteChartJacobianBounds (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance inverseChartNormedAddCommGroup (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance inverseChartNormedSpace (y : Model n) (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedSpace

def inverseChartJacobian (a : M) (z : Model n) : ℝ :=
  let F : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm z) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a).symm z
  F.toLinearMap.normDet

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_inverse_product (a : M) {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    chartJacobian (n := n) a ((extChartAt 𝓘(ℝ,Model n) a).symm z)*
      inverseChartJacobian (n := n) a z=1 := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  let F : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm z) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm z
  let G : TangentSpace 𝓘(ℝ,Model n) (d.symm z) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d (d.symm z)
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
  simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  change G.comp F=ContinuousLinearMap.id ℝ (Model n) at h
  have hn := congrArg (fun L : Model n →L[ℝ] Model n => L.toLinearMap.normDet) h
  change (G.toLinearMap ∘ₗ F.toLinearMap).normDet=(LinearMap.id : Model n →ₗ[ℝ] Model n).normDet at hn
  rw [LinearMap.normDet_comp_of_finrank_eq F.toLinearMap G.toLinearMap rfl,LinearMap.normDet_id] at hn
  exact hn

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_pos {a x : M} (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    0<chartJacobian (n := n) a x := by
  have h := chartJacobian_inverse_product a ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx] at h
  apply (chartJacobian_nonneg a x).lt_of_ne'
  intro he
  rw [he,zero_mul] at h
  exact zero_ne_one h

omit [CompactSpace M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma eventually_chartJacobian_bounds (a : M) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ᶠ x in 𝓝 a,
      l≤chartJacobian (n := n) a x ∧ chartJacobian (n := n) a x≤u := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,hCd⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨D,hD,hDi⟩ := eventually_norm_mfderivWithin_symm_extChartAt_comp_lt 𝓘(ℝ,Model n) a
  let N := Module.finrank ℝ (Model n)
  let U : ℝ := N.factorial * C ^ N
  let Q : ℝ := N.factorial * D ^ N
  have hU : 0<U := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hC _)
  have hQ : 0<Q := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hD _)
  refine ⟨Q⁻¹,U,inv_pos.mpr hQ,hU,?_⟩
  filter_upwards [hCd,hDi,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a] with x hxC hxD hxs
  let F : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d x
  let G : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm (d x)) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm (d x)
  have hF : ‖F‖≤C := hxC.le
  have hG : ‖G‖≤D := by
    simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hxD
    exact hxD.le
  have hFU : F.toLinearMap.normDet≤U :=
    (normDet_le_factorial_opNorm F rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hF _) (Nat.cast_nonneg _))
  have hGQ : G.toLinearMap.normDet≤Q :=
    (normDet_le_factorial_opNorm G rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hG _) (Nat.cast_nonneg _))
  have hp := chartJacobian_inverse_product a (d.map_source hxs)
  rw [d.left_inv hxs] at hp
  refine ⟨?_,hFU⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hQ).mpr
  calc
    1=chartJacobian (n := n) a x*G.toLinearMap.normDet := hp.symm
    _ ≤ chartJacobian (n := n) a x*Q := mul_le_mul_of_nonneg_left hGQ (chartJacobian_nonneg a x)

end ChartJacobianBounds
end WeakMTWTransport

end

end

end

end OAI
