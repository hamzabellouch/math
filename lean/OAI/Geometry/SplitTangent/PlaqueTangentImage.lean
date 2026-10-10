import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Plaque Tangent Image. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u v
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {Y : ComplexManifold.{v}} {S : TangentSplitting X}
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma mfderiv_into_first (P : AlignedProductChart S A B) {f : Y.Carrier → X.Carrier}
    {y : Y.Carrier} (hf : ContMDiffAt (ModelWithCorners Y) (ModelWithCorners X) ω f y)
    (hy : f y∈P.chart.source)
    (hplaque : ∀ᶠ z in 𝓝 y,(P.chart (f z)).2=(P.chart (f y)).2)
    (v : Tangent Y y) :
    mfderiv (ModelWithCorners Y) (ModelWithCorners X) f y v∈S.first (f y) := by
  have hp := P.holomorphicAt hy
  have hcomp := hp.comp y hf
  have hzero : mfderiv (ModelWithCorners Y) 𝓘(ℂ,B) (fun z => (P.chart (f z)).2) y=0 := by
    have he : (fun z => (P.chart (f z)).2) =ᶠ[𝓝 y] (fun _ => (P.chart (f y)).2) := hplaque
    rw [he.mfderiv_eq,mfderiv_const]
    simp
  have hds := mfderiv_comp y ((ContinuousLinearMap.snd ℂ A B).differentiableAt.mdifferentiableAt)
    (hcomp.mdifferentiableAt (by simp))
  have hdc := mfderiv_comp y (hp.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have hs : (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (f y)
      (mfderiv (ModelWithCorners Y) (ModelWithCorners X) f y v)).2=0 := by
    have he := DFunLike.congr_fun hzero v
    change mfderiv (ModelWithCorners Y) 𝓘(ℂ,B) ((ContinuousLinearMap.snd ℂ A B) ∘ P.chart ∘ f) y v=0 at he
    rw [hds,hdc,mfderiv_eq_fderiv] at he
    simp only [ContinuousLinearMap.fderiv] at he
    exact he
  have hm : mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (f y)
      (mfderiv (ModelWithCorners Y) (ModelWithCorners X) f y v) ∈
      Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (f y)).toLinearMap
        (S.first (f y)) := by
    rw [P.first _ hy]
    exact hs
  obtain ⟨w,hw,he⟩ := hm
  have he' := P.mdifferentiable.mfderiv_injective hy he
  exact he' ▸ hw

end SplitTangent.AlignedProductChart

end

end OAI
