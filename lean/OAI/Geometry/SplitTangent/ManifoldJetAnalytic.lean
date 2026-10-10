import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.TwistedCurveTensor
import OAI.Geometry.SplitTangent.ManifoldLeafJets

namespace OAI

/-! Manifold Jet Analytic. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma derivative_coordinates_analytic (P : AlignedProductChart S A B)
    {g : ℂ → X.Carrier} {z₀ : ℂ}
    (hg : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g z₀)
    (hy : g z₀∈P.chart.source) :
    AnalyticAt ℂ (F := Model X →L[ℂ] A × B) (fun z : ℂ =>
      ((mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (g z) : Model X →L[ℂ] A × B).comp
        ((trivializationAt (Model X) (Tangent X) (g z₀)).symmL ℂ (g z)) : Model X →L[ℂ] A × B)) z₀ := by
  let c := chartAt (Model X) (g z₀)
  let t := trivializationAt (Model X) (Tangent X) (g z₀)
  have hc0 : g z₀∈c.source := mem_chart_source _ _
  have hcinv := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (g z₀))
    (c.map_source hc0)
  have hP : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,A × B) ω P.chart (c.symm (c (g z₀))) := by
    simpa only [c.left_inv hc0] using P.holomorphicAt hy
  have hpc : AnalyticAt ℂ (P.chart ∘ c.symm) (c (g z₀)) :=
    (hP.comp _ hcinv).contDiffAt.analyticAt
  have hcg : AnalyticAt ℂ (c ∘ g) z₀ :=
    ((contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (g z₀)) hc0).comp _ hg).contDiffAt.analyticAt
  have h := AnalyticAt.comp (g := fderiv ℂ (P.chart ∘ c.symm)) (f := c ∘ g) hpc.fderiv hcg
  apply h.congr
  filter_upwards [hg.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hc0),
    hg.continuousAt.preimage_mem_nhds (P.chart.open_source.mem_nhds hy)] with z hcz hpz
  have ht : t.symmL ℂ (g z)=mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c (g z)) := by
    simpa [t,c,extChartAt_coe_symm,extChartAt_coe,ModelWithCorners] using
      (TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) hcz)
  have hci := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (g z₀))
    (c.map_source hcz)).mdifferentiableAt (by simp)
  have hpi : MDifferentiableAt (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (c.symm (c (g z))) := by
    simpa only [c.left_inv hcz] using (P.holomorphicAt hpz).mdifferentiableAt (by simp)
  change fderiv ℂ (P.chart ∘ c.symm) (c (g z))=_
  rw [←mfderiv_eq_fderiv,mfderiv_comp _ hpi hci,c.left_inv hcz,←ht]
  rfl

 
lemma jet_analytic (P : AlignedProductChart S A B)
    {g : ℂ → X.Carrier} {z₀ : ℂ} {f : X.Carrier → ℂ}
    (hg : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g z₀)
    (hy : g z₀∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f (g z₀)) (m : ℕ) :
    AnalyticAt ℂ (tangentTensorCoordinates g (fun z => P.jet f (g z) m) z₀) z₀ := by
  have hv := AnalyticAt.comp (f := P.chart ∘ g) (g := fun y => HorizontalJet.value (f ∘ P.chart.symm) y m)
    (HorizontalJet.analytic_value (P.coordinate_function_analytic hy hf) m)
    (((P.holomorphicAt hy).comp _ hg).contDiffAt.analyticAt)
  have hd := P.derivative_coordinates_analytic hg hy
  have hdp : AnalyticAt ℂ (F := Fin m → (Model X →L[ℂ] A × B)) (fun z : ℂ => fun _ : Fin m =>
      ((mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (g z) : Model X →L[ℂ] A × B).comp
        ((trivializationAt (Model X) (Tangent X) (g z₀)).symmL ℂ (g z)) : Model X →L[ℂ] A × B)) z₀ :=
    analyticAt_pi_iff.mpr fun _ => hd
  have hh := ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap.comp
    (hdp.prod hv)
  exact hh

 

lemma jet_parameter_analytic (P : AlignedProductChart S A B)
    {g : ℂ → X.Carrier} {z₀ : ℂ} {f : ℂ × X.Carrier → ℂ}
    (hg : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g z₀)
    (hy : g z₀∈P.chart.source)
    (hf : ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω f (z₀,g z₀))
    (m : ℕ) :
    AnalyticAt ℂ (tangentTensorCoordinates g
      (fun z => P.jet (fun x => f (z,x)) (g z) m) z₀) z₀ := by
  let h : ℂ × (A × B) → ℂ := fun w => f (w.1,P.chart.symm w.2)
  have hf' : ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω
      f (z₀,P.chart.symm (P.chart (g z₀))) := by
    simpa only [P.chart.left_inv hy] using hf
  have hh : AnalyticAt ℂ h (z₀,P.chart (g z₀)) := by
    have hi : ContMDiffAt 𝓘(ℂ,ℂ × (A × B)) (ModelWithCorners X) ω
        (fun w : ℂ × (A × B) => P.chart.symm w.2) (z₀,P.chart (g z₀)) :=
      (P.inverse_holomorphicAt (P.chart.map_source hy)).comp (z₀,P.chart (g z₀))
        (show ContMDiffAt 𝓘(ℂ,ℂ × (A × B)) 𝓘(ℂ,A × B) ω Prod.snd _ from
          contDiff_snd.contDiffAt.contMDiffAt)
    exact (hf'.comp (z₀,P.chart (g z₀))
      ((show ContMDiffAt 𝓘(ℂ,ℂ × (A × B)) 𝓘(ℂ,ℂ) ω Prod.fst _ from
        contDiff_fst.contDiffAt.contMDiffAt).prodMk hi)).contDiffAt.analyticAt
  have hv := HorizontalJet.analytic_parameter_value (g := P.chart ∘ g) hh
    (((P.holomorphicAt hy).comp _ hg).contDiffAt.analyticAt) m
  have hd := P.derivative_coordinates_analytic hg hy
  have hdp : AnalyticAt ℂ (F := Fin m → (Model X →L[ℂ] A × B))
      (fun z : ℂ => fun _ : Fin m =>
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (g z) : Model X →L[ℂ] A × B).comp
        ((trivializationAt (Model X) (Tangent X) (g z₀)).symmL ℂ (g z))) z₀ :=
    analyticAt_pi_iff.mpr fun _ => hd
  exact ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap.comp
    (hdp.prod hv)

end SplitTangent.AlignedProductChart

end

end OAI
