import Mathlib
import OAI.Geometry.WeakMTW.Potentials.GradientCoordinates

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

 abbrev CovectorParameters (n : ℕ) := ℝ × (Model n × (Model n →L[ℝ] ℝ))
 local instance realNormedParams : NormedSpace ℝ (Model n) := inferInstance

 def covectorFlow (z : M) (A : CovectorParameters n) : TangentBundle (model n) M :=
   geodesicFlow (-A.1) ((stateChart z).symm (A.2.1,(metric z A.2.1).inverse A.2.2))

 theorem covectorFlow_smooth (z : M) {A : CovectorParameters n}
     (hA : A.2.1 ∈ (chartAt (Model n) z).target) :
     ContMDiffAt 𝓘(ℝ,CovectorParameters n) ((model n).prod (model n)) ∞ (covectorFlow z) A := by
   let c := chartAt (Model n) z
   have hG : ContDiffAt ℝ ∞ (fun B : CovectorParameters n => (metric z B.2.1).inverse) A :=
     (((contDiffOn_metric_inverse c.open_target (metric_smooth z)
       (fun X hX v hv => metric_positive z hX hv)) A.2.1 hA).contDiffAt
       (c.open_target.mem_nhds hA)).comp A contDiffAt_snd.fst
   have hP : ContDiffAt ℝ ∞ (fun B : CovectorParameters n =>
       (B.2.1,(metric z B.2.1).inverse B.2.2)) A :=
     contDiffAt_snd.fst.prodMk (hG.clm_apply contDiffAt_snd.snd)
   have hT : (A.2.1,(metric z A.2.1).inverse A.2.2) ∈ (stateChart z).target :=
     (stateChart_target z _).mpr hA
   have hsym : ContMDiffOn 𝓘(ℝ,Model n × Model n) ((model n).prod (model n)) ∞
       (stateChart z).symm (stateChart (E := Model n) z).target := by
     rw [modelWithCornersSelf_prod]
     exact contMDiffOn_chart_symm (I := (model n).prod (model n))
       (x := (⟨z,0⟩ : TangentBundle (model n) M))
   have hS : ContMDiffAt 𝓘(ℝ,CovectorParameters n) ((model n).prod (model n)) ∞
       (fun B : CovectorParameters n => (stateChart z).symm (B.2.1,(metric z B.2.1).inverse B.2.2)) A :=
     (hsym.contMDiffAt ((stateChart z).open_target.mem_nhds hT)).comp A
       (contMDiffAt_iff_contDiffAt.mpr hP)
   exact geodesicFlow_smooth.contMDiffAt.comp A
     ((contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst.neg).prodMk hS)

 def intermediateInverse (hMTW : HasWeakMTW (n := n) (M := M)) {u : M → ℝ}
     (hu : IsPotential u) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (z : M) : TangentBundle (model n) M :=
   ((potentialHomeomorph hMTW hu ht ht1).symm z).val

 theorem intermediateInverse_continuous (hMTW : HasWeakMTW (n := n) (M := M)) {u : M → ℝ}
     (hu : IsPotential u) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
     Continuous (intermediateInverse hMTW hu ht ht1) :=
   continuous_subtype_val.comp (potentialHomeomorph hMTW hu ht ht1).symm.continuous

 theorem covectorFlow_eq_inverse (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
     (z y : M) (hy : y ∈ (chartAt (Model n) z).source) :
     covectorFlow z (t,chartAt (Model n) z y,
       fderiv ℝ (fun X => hopfLax t u ((chartAt (Model n) z).symm X)) (chartAt (Model n) z y)) =
       intermediateInverse hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1 y := by
   have hq : (⟨y,normalGradient (hopfLax t u) y⟩ : TangentBundle (model n) M) ∈ (stateChart z).source :=
     (stateChart_source z _).mpr hy
   have he : stateChart z (⟨y,normalGradient (hopfLax t u) y⟩ : TangentBundle (model n) M) =
       (chartAt (Model n) z y,(metric z (chartAt (Model n) z y)).inverse
         (fderiv ℝ (fun X => hopfLax t u ((chartAt (Model n) z).symm X)) (chartAt (Model n) z y))) := by
     apply Prod.ext
     · rfl
     · exact normalGradient_coordinates (intermediate_c11 hMTW huv ht ht1).1 z y hy
   unfold covectorFlow
   rw [←he,(stateChart z).left_inv hq]
   exact (intermediate_pole_flow hMTW huv ht ht1 y).symm
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
