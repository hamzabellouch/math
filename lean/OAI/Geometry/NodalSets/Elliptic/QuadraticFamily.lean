import OAI.Geometry.NodalSets.Charts.FrameMapFamily
import OAI.Geometry.NodalSets.Elliptic.SpatialJetFamily

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev QuadParam (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × ((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E))

def rawQuadratic (p : QuadParam E) (x : E) : E :=
  p.1 + p.2.1 x - (1/2:ℝ) • p.2.2 x x

lemma rawQuadratic_smooth :
    ContDiff ℝ ∞ (Function.uncurry (rawQuadratic (E := E))) := by
  exact (contDiff_fst.fst.add (contDiff_fst.snd.fst.clm_apply contDiff_snd)).sub
    ((contDiff_fst.snd.snd.clm_apply contDiff_snd).clm_apply contDiff_snd |>.const_smul (1/2:ℝ))

lemma rawQuadratic_eq (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    rawQuadratic (y, e.toContinuousLinearMap, B) = quadraticChartMap y e B := rfl

def pulledForm (g : E → E →L[ℝ] E →L[ℝ] ℝ) (p : QuadParam E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let J := fderiv ℝ (rawQuadratic p) x
  (((ContinuousLinearMap.compL ℝ E E ℝ).flip J).comp (g (rawQuadratic p x))).comp J

lemma pulledForm_apply (g : E → E →L[ℝ] E →L[ℝ] ℝ) (p : QuadParam E) (x u v : E) :
    pulledForm g p x u v = pullbackMetric g (rawQuadratic p) x u v := rfl

lemma pulledForm_smooth (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (Function.uncurry (pulledForm g)) := by
  let J : QuadParam E × E → E →L[ℝ] E := fun z ↦ fderiv ℝ (rawQuadratic z.1) z.2
  have hJ : ContDiff ℝ ∞ J :=
    smooth_spatial_fderiv (rawQuadratic (E := E)) rawQuadratic_smooth
  have hG : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦ g (rawQuadratic z.1 z.2)) :=
    hg.comp rawQuadratic_smooth
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip
  have hL₀ : ContDiff ℝ ∞ (fun A : E →L[ℝ] E ↦ L A) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E)
      (F := (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) L
  have hL : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      (ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)) :=
    hL₀.comp hJ
  have hC : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)).comp (g (rawQuadratic z.1 z.2))) :=
    hL.clm_comp hG
  exact hC.clm_comp hJ

variable {T : Type*} [TopologicalSpace T]

theorem quadratic_family_spatial_jets (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
  continuous_spatial_jets_of_smooth_family rawQuadratic rawQuadratic_smooth
    (fun t ↦ (y t, (e t).toContinuousLinearMap, B t)) (hy.prodMk (he.prodMk hB)) k

theorem charted_scalar_spatial_jets (S : E → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k
      (S ∘ quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
  continuous_spatial_jets_of_smooth_family (fun p x ↦ S (rawQuadratic p x))
    (hS.comp rawQuadratic_smooth) (fun t ↦ (y t, (e t).toContinuousLinearMap, B t))
    (hy.prodMk (he.prodMk hB)) k

theorem pulled_metric_spatial_jets (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k
      (pulledForm g (y z.1, (e z.1).toContinuousLinearMap, B z.1)) z.2) :=
  continuous_spatial_jets_of_smooth_family (pulledForm g) (pulledForm_smooth g hg)
    (fun t ↦ (y t, (e t).toContinuousLinearMap, B t)) (hy.prodMk (he.prodMk hB)) k

end
end Yau.Geometry

end OAI
