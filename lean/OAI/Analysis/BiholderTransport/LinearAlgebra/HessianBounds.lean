import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianCoordinates
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactLocalPositiveBounds

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section HessianBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventually_normalHessian_bounds {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 c,
      ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖ := by
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let U := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V := (Model n×Model n)×Model n
  let : NormedAddCommGroup V := inferInstanceAs (NormedAddCommGroup ((Model n×Model n)×Model n))
  let : NormedSpace ℝ V := inferInstanceAs (NormedSpace ℝ ((Model n×Model n)×Model n))
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : SeminormedAddGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let B : TangentBundle 𝓘(ℝ,Model n) M → (V →L[ℝ] V →L[ℝ] ℝ) := fun z =>
    fderiv ℝ (fderiv ℝ (coordinateNormalCost c)) (χ z,0)
  have hG := (coordinateNormalCost_contDiffAt c c (mem_extChartAt_source c) hc).of_le
    (m := 3) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hD : ContinuousAt (fderiv ℝ (fderiv ℝ (coordinateNormalCost c))) (χ c,(0:Model n)) :=
    ((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt
  have hχ := (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (n := ∞) (x := c)).continuousAt
  have hmap : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,Model n) M => (χ z,(0:Model n))) c :=
    hχ.prodMk continuousAt_const
  have hBc : ContinuousAt B c := ContinuousAt.comp
    (f := fun z : TangentBundle 𝓘(ℝ,Model n) M => (χ z,(0:Model n)))
    (g := fderiv ℝ (fderiv ℝ (coordinateNormalCost c))) hD hmap
  have hBb : ∀ᶠ z in 𝓝 c, ‖B z‖<‖B c‖+1 := hBc.norm.eventually
    (gt_mem_nhds (by linarith : ‖B c‖<‖B c‖+1))
  obtain ⟨CU,hCU,hUb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    (Bundle.contMDiff_proj (n := ∞) (IB := 𝓘(ℝ,Model n)) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).continuous
  refine ⟨(‖B c‖+1)*CU*CU,by positivity,?_⟩
  filter_upwards [hBb,hproj.continuousAt.eventually hUb,
    extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c,
    isOpen_total_injectivityDomain.mem_nhds hc] with z hz hU hzχ hzI
  intro v w
  rw [normalHessian_coordinate_form c z hzχ hzI v w]
  change ‖B z (0,U.continuousLinearMapAt ℝ z.1 v) (0,U.continuousLinearMapAt ℝ z.1 w)‖≤_
  have hv : ‖(U.continuousLinearMapAt ℝ z.1) v‖≤CU*‖v‖ :=
    ((U.continuousLinearMapAt ℝ z.1).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hU.le (norm_nonneg v))
  have hw : ‖(U.continuousLinearMapAt ℝ z.1) w‖≤CU*‖w‖ :=
    ((U.continuousLinearMapAt ℝ z.1).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hU.le (norm_nonneg w))
  have hv' : ‖((0:Model n×Model n),U.continuousLinearMapAt ℝ z.1 v)‖≤CU*‖v‖ := by simpa using hv
  have hw' : ‖((0:Model n×Model n),U.continuousLinearMapAt ℝ z.1 w)‖≤CU*‖w‖ := by simpa using hw
  calc
    _ ≤ ‖B z‖*‖(0,U.continuousLinearMapAt ℝ z.1 v)‖*‖(0,U.continuousLinearMapAt ℝ z.1 w)‖ :=
      ((B z _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        ((B z).le_opNorm _) (norm_nonneg _))
    _ ≤ (‖B c‖+1)*(CU*‖v‖)*(CU*‖w‖) :=
      mul_le_mul (mul_le_mul hz.le hv' (norm_nonneg _) (by positivity)) hw'
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma compact_normalHessian_bounds {K : Set (TangentBundle 𝓘(ℝ,Model n) M)}
    (hK : IsCompact K) (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ C : ℝ, 0<C ∧ ∀ z∈K, ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖ := by
  obtain ⟨r,C,hr,hC,H⟩ := compact_local_positive_bounds
    (P := fun (_ : ℝ) C z => ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖) hK (by
        intro r R b B hr hrR hbB z hz v w
        exact (hz v w).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbB (norm_nonneg v)) (norm_nonneg w))) (by
        intro z hz
        obtain ⟨C,hC,H⟩ := eventually_normalHessian_bounds (hI z hz)
        exact ⟨1,C,by norm_num,hC,H⟩)
  exact ⟨C,hC,H⟩

lemma uniform_prefixHessian_bounds :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∀ v w : TangentSpace 𝓘(ℝ,Model n) x,
      |normalHessian x (t • p) v w|≤C*‖v‖*‖w‖ := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let S := Icc (1/4:ℝ) (3/4) ×ˢ G
  let P : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 q.2
  have hP : Continuous P := contMDiff_tangentScale.continuous
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))
  obtain ⟨C,hC,H⟩ := compact_normalHessian_bounds (hS.image hP) (by
    intro w hw
    rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
    exact contracted_minimizer_mem_injectivityDomain htz.2 (by linarith [htz.1.1])
      (by linarith [htz.1.2]))
  refine ⟨C,hC,?_⟩
  intro x p hp t ht
  exact H (P (t,⟨x,p⟩)) (mem_image_of_mem _ ⟨ht,hp⟩)

end HessianBounds
end WeakMTWTransport

end

end

end

end OAI
