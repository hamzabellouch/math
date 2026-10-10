import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import OAI.Geometry.NodalSets.Elliptic.AmbientDerivativeDistance

namespace OAI

namespace Yau.Geometry
open Bundle Manifold Set Filter ContinuousLinearMap
open scoped ENNReal NNReal ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eventually_norm_mfderiv_map_lt (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (x : M) : ∃ C > 0, ∀ᶠ y in 𝓝 x,
      Norm.norm (E := TangentSpace I y →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f y) < C := by
  let D := inTangentCoordinates I 𝓘(ℝ,F) id f (mfderiv I 𝓘(ℝ,F) f) x
  have hD : ContinuousAt D x := ((hf x).mfderiv_const (m := 0) (by simp)).continuousAt
  obtain ⟨K,hK,hchart⟩ := eventually_norm_mfderiv_extChartAt_lt I x
  refine ⟨(‖D x‖+1)*K, by positivity, ?_⟩
  have hlocal : ∀ᶠ y in 𝓝 x, ‖D y‖ < ‖D x‖+1 :=
    hD.norm.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hlocal,hchart,chart_source_mem_nhds H x] with y hy hcy hsrc
  have hdecomp : mfderiv I 𝓘(ℝ,F) f y =
      (D y).comp (mfderiv I 𝓘(ℝ,E) (extChartAt I x) y) := by
    let d : E →L[ℝ] F := mfderiv I 𝓘(ℝ,F) f y
    let A : F →L[ℝ] F := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F)
      (extChartAt 𝓘(ℝ,F) (f x)) (f y)
    let B : E →L[ℝ] E := mfderivWithin 𝓘(ℝ,E) I
      (extChartAt I x).symm (range I) (extChartAt I x y)
    let C : E →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) y
    have hA : A = ContinuousLinearMap.id ℝ F := by
      change (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) id (f y) : F →L[ℝ] F) = _
      exact mfderiv_id
    have hcoord : D y = A.comp (d.comp B) :=
      inTangentCoordinates_eq_mfderiv_comp_abuse (I := I) (I' := 𝓘(ℝ,F))
        (f := id) (g := f) (ϕ := mfderiv I 𝓘(ℝ,F) f)
        (x₀ := x) (x := y) hsrc (mem_univ _)
    have hBC : B.comp C = ContinuousLinearMap.id ℝ E :=
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := I) (x := x) (y := y) (by simpa only [extChartAt_source] using hsrc)
    ext v
    change d v = D y (C v)
    have hv := congrArg (fun L : E →L[ℝ] F ↦ L (C v)) hcoord
    have hbc := congrArg (fun L : E →L[ℝ] E ↦ L v) hBC
    change B (C v) = v at hbc
    simpa only [hA, comp_apply, id_apply, hbc] using hv.symm
  rw [hdecomp]
  apply (opNorm_comp_le _ _).trans_lt
  let P : TangentSpace I y →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) y
  have hP : ‖P‖ < K := hcy
  exact (mul_le_mul_of_nonneg_right hy.le (norm_nonneg P)).trans_lt
    (mul_lt_mul_of_pos_left hP (by positivity))

lemma compact_norm_mfderiv_bound (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x ∈ K,
      ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C := by
  classical
  choose c hc hloc using eventually_norm_mfderiv_map_lt f hf
  obtain ⟨t,ht,hcover⟩ := hK.elim_nhds_subcover
    (fun x ↦ {y | Norm.norm (E := TangentSpace I y →L[ℝ] F)
      (mfderiv I 𝓘(ℝ,F) f y) < c x}) (fun x _ ↦ hloc x)
  let C : ℝ := 1 + ∑ x ∈ t, c x
  have hC : 0 < C := by
    dsimp [C]
    have := Finset.sum_nonneg (fun x (_ : x ∈ t) ↦ (hc x).le)
    linarith
  refine ⟨⟨C,hC.le⟩,hC,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hle : c y ≤ ∑ z ∈ t, c z := Finset.single_le_sum (fun z _ ↦ (hc z).le) hy
  let L : TangentSpace I x →L[ℝ] F := mfderiv I 𝓘(ℝ,F) f x
  have hbound : ‖L‖ ≤ C := by
    change ‖L‖ < c y at hxy
    dsimp [C]; linarith
  exact (ofReal_norm (E := TangentSpace I x →L[ℝ] F) L).symm.le.trans
    ((ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_eq_coe_nnreal hC.le))

lemma compact_map_edist_bound [CompactSpace M] (f : M → F)
    (hf : ContMDiff I 𝓘(ℝ,F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  obtain ⟨C,hpos,hC⟩ := compact_norm_mfderiv_bound f hf isCompact_univ
  exact ⟨C,hpos,map_edist_le_riemannianEDist f hf C hpos (fun x ↦ hC x (mem_univ x))⟩

end
end Yau.Geometry

end OAI
