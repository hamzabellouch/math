import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateParameterFamily
import OAI.Geometry.WeakMTW.Potentials.UniformLocalLipschitz
import OAI.Geometry.WeakMTW.Potentials.CompactSmoothControl

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem datumInverse_minimizing (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hb : b < 1) (d : IntermediateDatum M a b) (y : M) :
     datumInverse hMTW ha hb d y ∈ totalMinimizingSet := by
   let q := (potentialHomeomorph hMTW ⟨d.v,d.dual.2.1,d.dual.2.2.1⟩
     (ha.trans_le d.time.1) (d.time.2.trans_lt hb)).symm y
   exact ((globalSupportingProperty hMTW ⟨d.v,d.dual.2.1,d.dual.2.2.1⟩).1
     q.val.1 q.val.2 q.property).1

 theorem covectorFlow_momentum_smooth (z x : M) {A : CovectorParameters n}
     (hA : A.2.1 ∈ (chartAt (Model n) z).target)
     (hx : (covectorFlow z A).1 ∈ (chartAt (Model n) x).source) :
     ContDiffAt ℝ ∞ (fun B => (stateChart x (covectorFlow z B)).2) A := by
   have hp : covectorFlow z A ∈ (stateChart x).source := (stateChart_source x _).mpr hx
   have hc : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ,Model n × Model n) ∞
       (stateChart x) (stateChart x).source :=
     contMDiffOn_extChartAt (I := (model n).prod (model n))
       (x := (⟨x,0⟩ : TangentBundle (model n) M))
   exact (contMDiffAt_iff_contDiffAt.mp
     (((hc _ hp).contMDiffAt ((stateChart x).open_source.mem_nhds hp)).comp A
       (covectorFlow_smooth z hA))).snd

 theorem intermediate_uniform_momentum_patch (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
     (x : M) {P : Set M} (hP : IsCompact P) (hPS : P ⊆ (chartAt (Model n) x).source) :
     ∃ C : ℝ≥0, ∀ d : IntermediateDatum M a b,
       LipschitzOnWith C (fun z => (stateChart x (datumInverse hMTW ha hb d z)).2)
         {z | (datumInverse hMTW ha hb d z).1 ∈ P} := by
   let f (d : IntermediateDatum M a b) (z : M) := (stateChart x (datumInverse hMTW ha hb d z)).2
   let S (d : IntermediateDatum M a b) : Set M := {z | (datumInverse hMTW ha hb d z).1 ∈ P}
   have hloc (z : M) : ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧
       ∀ d : IntermediateDatum M a b, LipschitzOnWith C (f d) (Metric.ball z r ∩ S d) := by
     obtain ⟨K,hK,hKt,r,A,hr,hsrc,hparam⟩ := intermediate_parameter_family hMTW ha hab hb z
     let K' := K ∩ (fun B => (covectorFlow z B).1) ⁻¹' P
     have hcont : ContinuousOn (fun B => (covectorFlow z B).1) K := by
       intro B hB
       exact ((FiberBundle.continuous_proj (Model n) (TangentSpace (model n))).continuousAt.comp
         (covectorFlow_smooth z (hKt B hB)).continuousAt).continuousWithinAt
     have hK' : IsCompact K' := CompactSmoothControl.compact_filter hK hcont hP.isClosed
     obtain ⟨C,hC⟩ := CompactSmoothControl.compact_lipschitz hK'
       (fun B hB => (covectorFlow_momentum_smooth z x (hKt B hB.1) (hPS hB.2)).of_le (by simp))
     have hmaps (d : IntermediateDatum M a b) :
         MapsTo (datumParameter (n := n) z d) (Metric.ball z r ∩ S d) K' := by
       intro y hy
       refine ⟨(hparam d).1 hy.1,?_⟩
       change (covectorFlow z (datumParameter z d y)).1 ∈ P
       rw [datumParameter_flow hMTW ha hb z d (hsrc hy.1)]
       exact hy.2
     refine ⟨r,C*A,hr,?_⟩
     intro d
     have hL := hC.comp ((hparam d).2.mono inter_subset_left) (hmaps d)
     apply LipschitzOnWith.of_dist_le_mul
     intro y hy w hw
     have hh := hL.dist_le_mul (x := y) hy (y := w) hw
     simpa only [Function.comp_apply,datumParameter_flow hMTW ha hb z d (hsrc hy.1),
       datumParameter_flow hMTW ha hb z d (hsrc hw.1)] using hh
   let G := totalMinimizingSet (n := n) (M := M) ∩ (Bundle.TotalSpace.proj) ⁻¹' P
   have hG : IsCompact G := totalMinimizingSet_compact.inter_right
      (hP.isClosed.preimage (FiberBundle.continuous_proj (Model n) (TangentSpace (model n))))
   have hGS : G ⊆ (stateChart x).source := fun _ hq => (stateChart_source x _).mpr (hPS hq.2)
   let B := (fun q : TangentBundle (model n) M => (stateChart x q).2) '' G
   have hB : IsCompact B := hG.image_of_continuousOn (((stateChart x).continuousOn.mono hGS).snd)
   refine UniformLocalLipschitz.globalize hloc (Metric.diam_nonneg (s := B)) ?_
   intro d y hy w hw
   apply Metric.dist_le_diam_of_mem hB.isBounded
   · exact ⟨datumInverse hMTW ha hb d y,⟨datumInverse_minimizing hMTW ha hb d y,hy⟩,rfl⟩
   · exact ⟨datumInverse hMTW ha hb d w,⟨datumInverse_minimizing hMTW ha hb d w,hw⟩,rfl⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
