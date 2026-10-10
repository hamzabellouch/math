import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.FormalBoxes

namespace OAI

/-! Twisted Curve Tensor. -/

noncomputable section
open Set Filter Topology Bundle
open scoped ContDiff Manifold
universe u
namespace SplitTangent

abbrev TangentTensor (X : ComplexManifold.{u}) (m : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin m => Model X) ℂ

 
def tangentTensorCoordinates {X : ComplexManifold.{u}} {m : ℕ}
    (g : ℂ → X.Carrier) (A : ℂ → TangentTensor X m) (z₀ : ℂ) (z : ℂ) :
    TangentTensor X m :=
  (A z).compContinuousLinearMap (fun _ =>
    (trivializationAt (Model X) (Tangent X) (g z₀)).symmL ℂ (g z))

 

structure TwistedCurveTensor {X : ComplexManifold.{u}} (g : RationalCurve X) (d : ℤ) (m : ℕ) where
  finite : ℂ → TangentTensor X m
  infinity : ℂ → TangentTensor X m
  finite_holomorphic : ∀z₀, AnalyticAt ℂ (tangentTensorCoordinates g.finite finite z₀) z₀
  infinity_holomorphic : ∀z₀, AnalyticAt ℂ (tangentTensorCoordinates g.infinity infinity z₀) z₀
  overlap : ∀z : ℂ, z≠0 → finite z = z^d • infinity z⁻¹

 

lemma section_coordinates_analytic {X : ComplexManifold.{u}} {g : ℂ → X.Carrier}
    {v : ∀z, Tangent X (g z)}
    (hv : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z =>
      ((trivializationAt (Model X) (Tangent X) (g z₀))
        (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2) z₀ := by
  let t := trivializationAt (Model X) (Tangent X) (g z₀)
  have hz : g z₀∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hs : (⟨g z₀,v z₀⟩ : TangentBundle (ModelWithCorners X) X.Carrier)∈t.source := by
    simpa only [t.mem_source] using hz
  exact ((t.contMDiffAt_iff (f := fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) hs).mp (hv z₀)).2.contDiffAt.analyticAt

lemma tangentTensor_contract_analytic {X : ComplexManifold.{u}} {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) {m : ℕ}
    {A : ℂ → TangentTensor X m} {z₀ : ℂ}
    (hA : AnalyticAt ℂ (tangentTensorCoordinates g A z₀) z₀)
    (v : Fin m → ∀z, Tangent X (g z))
    (hv : ∀i,ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v i z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) :
    AnalyticAt ℂ (fun z => A z (fun i => v i z)) z₀ := by
  let t := trivializationAt (Model X) (Tangent X) (g z₀)
  let w (i : Fin m) (z : ℂ) := (t (⟨g z,v i z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  have hw : ∀i,AnalyticAt ℂ (w i) z₀ := fun i => section_coordinates_analytic (hv i) z₀
  have ha : AnalyticAt ℂ (fun z => tangentTensorCoordinates g A z₀ z (fun i => w i z)) z₀ :=
    (ContinuousLinearMap.id ℂ (TangentTensor X m)).analyticAt_uncurry_of_multilinear.comp
      (hA.prod (AnalyticAt.pi hw))
  apply ha.congr
  have hz : g z₀∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [(hg z₀).continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hz)] with z hz
  symm
  change A z (fun i => v i z) = A z (fun i => t.symmL ℂ (g z) (w i z))
  congr 1
  funext i
  change v i z=t.symmL ℂ (g z) (t (⟨g z,v i z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz]
  exact (t.symmL_continuousLinearMapAt hz _).symm

namespace TwistedCurveTensor
open DiagonalRationality PositiveTensor
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {d : ℤ} {m : ℕ}

 

def contract (A : TwistedCurveTensor g d m) (σ : Fin m → CurveTangentSection g) :
    lineSections d :=
  ⟨(fun z => A.finite z (fun i => (σ i).finite z),
    fun z => A.infinity z (fun i => (σ i).infinity z)),
    ⟨fun z => (tangentTensor_contract_analytic g.finite_holomorphic (A.finite_holomorphic z)
      (fun i => (σ i).finite) (fun i => (σ i).finite_holomorphic)).differentiableAt,
     fun z => (tangentTensor_contract_analytic g.infinity_holomorphic (A.infinity_holomorphic z)
      (fun i => (σ i).infinity) (fun i => (σ i).infinity_holomorphic)).differentiableAt,
     fun z hz => by
       simp only [A.overlap z hz]
       change z ^ d * (A.infinity z⁻¹) (fun i => (σ i).finite z) = _
       congr 2
       funext i
       exact (σ i).overlap z hz⟩⟩

 

theorem contract_zero {d : ℕ} (A : TwistedCurveTensor g (d : ℤ) m)
    (hdm : d < m) (σ : Fin m → CurveTangentSection g)
    (hσ0 : ∀i,(σ i).finite 0=0) : A.contract σ=0 := by
  let t := trivializationAt (Model X) (Tangent X) (g.finite 0)
  let w (i : Fin m) (z : ℂ) :=
    (t (⟨g.finite z,(σ i).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  have hw : ∀i,AnalyticAt ℂ (w i) 0 :=
    fun i => section_coordinates_analytic (σ i).finite_holomorphic 0
  have hw0 : ∀i,w i 0=0 := by
    intro i
    change (t (⟨g.finite 0,(σ i).finite 0⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2=0
    rw [hσ0 i]
    rw [← t.continuousLinearMapAt_apply_of_mem ℂ (FiberBundle.mem_baseSet_trivializationAt' (g.finite 0))]
    exact map_zero _
  apply lineSection_zero_of_contraction hdm (A.contract σ)
    (tangentTensorCoordinates g.finite A.finite 0) (A.finite_holomorphic 0) w hw hw0
  have hz : g.finite 0∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
    (t.open_baseSet.mem_nhds hz)] with z hz
  change A.finite z (fun i => (σ i).finite z)=
    A.finite z (fun i => t.symmL ℂ (g.finite z) (w i z))
  congr 1
  funext i
  change (σ i).finite z=t.symmL ℂ (g.finite z)
    (t (⟨g.finite z,(σ i).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz]
  exact (t.symmL_continuousLinearMapAt hz _).symm

 

theorem vanish_on_generated_fiber {d : ℕ} (A : TwistedCurveTensor g (d : ℤ) m)
    {D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)} (hg : PointedGenerated g D)
    (hdm : d < m) (v : Fin m → Tangent X (g.finite 1)) (hv : ∀i,v i∈D (g.finite 1)) :
    A.finite 1 v=0 := by
  classical
  choose σ hσf hσi hσ0 hσ1 using fun i => hg (v i) (hv i)
  have hs := A.contract_zero hdm σ hσ0
  have h := congrArg (fun s : lineSections (d : ℤ) => s.val.1 1) hs
  change A.finite 1 (fun i => (σ i).finite 1)=0 at h
  simpa only [hσ1] using h

end TwistedCurveTensor
end SplitTangent

end

end OAI
