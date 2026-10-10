import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafPolynomialGrowth
import OAI.Geometry.SplitTangent.LeafHomogeneousRelations
import OAI.Geometry.SplitTangent.ProjectiveHypersurfaces

namespace OAI

/-! Leaf Closure Relations. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S)
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  (P : AlignedProductChart S A B)

lemma polynomialKernel_germIn {k : ℕ}
    {Q : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k}
    (hy : g.finite 1∈P.chart.source) (hQ : Q∈F.leafPolynomialKernel P k) :
    L.GermIn (e.homogeneousZeroLocus Q.val) (g.finite 1) := by
  apply (L.germIn_iff P hy).mpr
  have ha := e.linearFrame_denominator_eventually
    (fun i => (F.a i).eval 1) (F.finite_denominator_ne 1)
  let s : A → X.Carrier := fun t => P.chart.symm (t,(P.chart (g.finite 1)).2)
  have hs : ContinuousAt s (P.chart (g.finite 1)).1 :=
    (P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt.comp
      (f := fun t : A => (t,(P.chart (g.finite 1)).2)) (x := (P.chart (g.finite 1)).1)
      (continuousAt_id.prodMk continuousAt_const)
  have hae : ∀ᶠ t in 𝓝 (P.chart (g.finite 1)).1,
      (∑i,(F.a i).eval 1*(e.map (s t)).rep i)≠0 :=
    (by simpa only [s,P.chart.left_inv hy] using hs.tendsto :
      Tendsto s (𝓝 (P.chart (g.finite 1)).1) (𝓝 (g.finite 1))).eventually ha
  filter_upwards [hQ,hae] with t ht hta
  exact (e.linearFrame_zero_iff Q.property _ hta).mp ht

lemma polynomialKernel_closure_zero {k : ℕ}
    {Q : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k}
    (hy : g.finite 1∈P.chart.source) (hQ : Q∈F.leafPolynomialKernel P k) :
    ∀x∈closure (L.leaf (g.finite 1)),MvPolynomial.eval (e.map x).rep Q.val=0 :=
  L.closure_leaf_subset (e.homogeneousZeroLocus_locally_holomorphic Q.property)
    (e.homogeneousZeroLocus_isClosed Q.property) (F.polynomialKernel_germIn L P hy hQ)

include F in
 

theorem leaf_closure_relation
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first (g.finite 1))+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃p : MvPolynomial (Fin (Module.finrank ℂ (S.first (g.finite 1))+1)) ℂ,
      p≠0 ∧ ∀x∈closure (L.leaf (g.finite 1)), MvPolynomial.eval (e.map x).rep D.val≠0 →
        MvPolynomial.eval (fun i => MvPolynomial.eval (e.map x).rep (H i).val /
          MvPolynomial.eval (e.map x).rep D.val) p=0 := by
  obtain ⟨k,Q,hQ,p,hp,he⟩ := F.leaf_homogeneous_relation L P hy ht hg D H
  refine ⟨p,hp,?_⟩
  intro x hx hD
  have hz := F.polynomialKernel_closure_zero L P hy hQ x hx
  rw [he _ hD] at hz
  exact (mul_eq_zero_iff_left (pow_ne_zero k hD)).mp hz

end SplitTangent.RationalCurveFrames

end

end OAI
