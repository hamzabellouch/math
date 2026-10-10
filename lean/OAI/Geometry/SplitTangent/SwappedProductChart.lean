import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Swapped Product Chart. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

def swap (P : AlignedProductChart S A B) : AlignedProductChart S.swap B A := by
  let c := ContinuousLinearEquiv.prodComm ℂ A B
  let Q := P.chart.trans c.toHomeomorph.toOpenPartialHomeomorph
  have hsource {y : X.Carrier} (hy : y∈Q.source) : y∈P.chart.source := hy.1
  have htarget {y : B × A} (hy : y∈Q.target) : c.symm y∈P.chart.target := hy.2
  have hd {y : X.Carrier} (hy : y∈Q.source) :
      mfderiv (ModelWithCorners X) 𝓘(ℂ,B × A) Q y=
        c.toContinuousLinearMap.comp (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y) := by
    change mfderiv (ModelWithCorners X) 𝓘(ℂ,B × A) (c ∘ P.chart) y=_
    rw [mfderiv_comp y ((c.contDiff (n := ω)).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((P.holomorphicAt (hsource hy)).mdifferentiableAt (by simp)),mfderiv_eq_fderiv,
      ContinuousLinearEquiv.fderiv]
    rfl
  refine { chart := Q
           holomorphic := ?_
           inverse_holomorphic := ?_
           first := ?_
           second := ?_ }
  · intro y hy
    exact (c.contDiff.contMDiff.contMDiffAt.comp y (P.holomorphicAt (hsource hy))).contMDiffWithinAt
  · intro y hy
    exact ((P.inverse_holomorphicAt (htarget hy)).comp y
      c.symm.contDiff.contMDiff.contMDiffAt).contMDiffWithinAt
  · intro y hy
    rw [S.swap_first,hd hy]
    change Submodule.map (c.toLinearMap.comp
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap) (S.second y)=_
    erw [Submodule.map_comp,P.second y (hsource hy)]
    ext p
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hp
      exact ⟨p.swap,hp,Prod.swap_swap p⟩
  · intro y hy
    rw [S.swap_second,hd hy]
    change Submodule.map (c.toLinearMap.comp
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap) (S.first y)=_
    erw [Submodule.map_comp,P.first y (hsource hy)]
    ext p
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hp
      exact ⟨p.swap,hp,Prod.swap_swap p⟩

@[simp] lemma swap_apply (P : AlignedProductChart S A B) (y : X.Carrier) :
    P.swap.chart y=(P.chart y).swap := rfl
@[simp] lemma swap_symm_apply (P : AlignedProductChart S A B) (y : B × A) :
    P.swap.chart.symm y=P.chart.symm y.swap := rfl
@[simp] lemma swap_source (P : AlignedProductChart S A B) : P.swap.chart.source=P.chart.source := by
  ext y
  change (y∈P.chart.source ∧ P.chart y∈Set.univ) ↔ y∈P.chart.source
  simp
@[simp] lemma swap_target (P : AlignedProductChart S A B) (y : B × A) :
    y∈P.swap.chart.target ↔ y.swap∈P.chart.target := by
  change (y∈Set.univ ∧ y.swap∈P.chart.target) ↔ y.swap∈P.chart.target
  simp

end SplitTangent.AlignedProductChart

end

end OAI
