import Mathlib
import OAI.Geometry.SplitTangent.AmbientLeafSections
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafGermIdentity

namespace OAI

/-! Ambient Leaf Germ. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AmbientTransition
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X} {d : ℕ}
  (T : AmbientTransition g d) (L : LeafJetAtlas S)
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

lemma flat_all_jets (f : ambientSectionSpace T)
    (hf : f∈SeparatedQuotientFiltration.zeroPart (T.contact L)) (z : ℂ) (m : ℕ) :
    L.jet (fun x => f.val.1 (z,x)) (g.finite z) m=0 :=
  ((Submodule.mem_iInf _).mp hf (m+1)).1 z m (Nat.lt_succ_self m)

 
theorem flat_joint_germ (f : ambientSectionSpace T)
    (hf : f∈SeparatedQuotientFiltration.zeroPart (T.contact L))
    (ht : g.TangentTo S.first) (P : AlignedProductChart S A B)
    {z₀ : ℂ} (hy : g.finite z₀∈P.chart.source) :
    (fun q : ℂ × A => f.val.1 (q.1,P.chart.symm (q.2,(P.chart (g.finite z₀)).2)))
      =ᶠ[𝓝 (z₀,(P.chart (g.finite z₀)).1)] 0 := by
  let b := (P.chart (g.finite z₀)).2
  let c := fun z => (P.chart (g.finite z)).1
  have hc : ContinuousAt c z₀ :=
    ((P.holomorphicAt hy).comp z₀ (g.finite_holomorphic z₀)).continuousAt.fst
  have hP : ContMDiffAt 𝓘(ℂ,ℂ × A) (ModelWithCorners X) ω
      (fun q => P.chart.symm (q.2,b)) (z₀,c z₀) :=
    (P.inverse_holomorphicAt (P.chart.map_source hy)).comp (z₀,c z₀)
      ((contDiffAt_snd.prodMk contDiffAt_const).contMDiffAt)
  have hfe : ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω
      f.val.1 (z₀,P.chart.symm (c z₀,b)) := by
    simpa only [c,b,P.chart.left_inv hy] using f.property.1 z₀
  have hfa : AnalyticAt ℂ
      (fun q : ℂ × A => f.val.1 (q.1,P.chart.symm (q.2,b))) (z₀,c z₀) :=
    (hfe.comp (z₀,c z₀) ((contDiffAt_fst.contMDiffAt).prodMk hP)).contDiffAt.analyticAt
  apply AnalyticFlatFamily.joint_germ_zero hfa hc
  filter_upwards [P.tangent_curve_snd_eventually g.finite_holomorphic hy ht.1,
    (g.finite_holomorphic z₀).continuousAt.preimage_mem_nhds (P.chart.open_source.mem_nhds hy)] with z hz hPz
  have h := P.germ_zero_of_all_jets L hPz (LeafJetAtlas.parameter_slice (f.property.1 z))
    (T.flat_all_jets L f hf z)
  simpa only [hz,c,b] using h

end SplitTangent.AmbientTransition

end

end OAI
