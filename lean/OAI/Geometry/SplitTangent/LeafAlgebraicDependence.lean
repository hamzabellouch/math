import Mathlib
import OAI.Geometry.SplitTangent.BoxMonomials
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafPolynomialGrowth

namespace OAI

/-! Leaf Algebraic Dependence. -/

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

abbrev leafFrame (t : A) :=
  F.finite 1 (P.chart.symm (t,(P.chart (g.finite 1)).2))

omit [CompleteSpace A] [CompleteSpace B] in
lemma leafFrame_continuousAt (hy : g.finite 1∈P.chart.source) :
    ContinuousAt (F.leafFrame P) (P.chart (g.finite 1)).1 := by
  have hh := (P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt.comp
    (f := fun a : A => (a,(P.chart (g.finite 1)).2))
    (x := (P.chart (g.finite 1)).1)
    (continuousAt_id.prodMk continuousAt_const)
  have hf := (F.finite_holomorphicAt 1).continuousAt
  have he : P.chart.symm ((P.chart (g.finite 1)).1,(P.chart (g.finite 1)).2)=g.finite 1 :=
    P.chart.left_inv hy
  rw [←he] at hf
  exact hf.comp (f := fun a : A => P.chart.symm (a,(P.chart (g.finite 1)).2))
    (x := (P.chart (g.finite 1)).1) hh

include L in
 

theorem leaf_coordinates_dependent
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first)
    (j : Fin (e.N+1)) (hj : F.finite 1 (g.finite 1) j≠0)
    (v : Fin (Module.finrank ℂ (S.first (g.finite 1))+1) → Fin (e.N+1)) :
    ∃p : MvPolynomial (Fin (Module.finrank ℂ (S.first (g.finite 1))+1)) ℂ,
      p≠0 ∧ (fun t : A => MvPolynomial.eval (fun i => F.leafFrame P t (v i)/F.leafFrame P t j) p)
        =ᶠ[𝓝 (P.chart (g.finite 1)).1] 0 := by
  classical
  let r := Module.finrank ℂ (S.first (g.finite 1))
  let C := (F.degree+r+1)^r*(F.degree+1)
  obtain ⟨t,hbig⟩ := PolynomialGrowthArithmetic.box_exceeds C r
  let k := (r+1)*t
  obtain ⟨hfin,hbound⟩ := F.leaf_polynomial_growth L P hy ht hg k
  let := hfin
  let q : BoxMonomials.Box (r+1) t → F.LeafPolynomialGerms P k :=
    fun b => (F.leafPolynomialKernel P k).mkQ (BoxMonomials.homogeneous j v b)
  have hnot : ¬LinearIndependent ℂ q := by
    intro hlin
    have hcard := hlin.fintype_card_le_finrank
    have hc : (t+1)^(r+1) ≤ Module.finrank ℂ (F.LeafPolynomialGerms P k) := by
      simpa only [BoxMonomials.Box,Fintype.card_fun,Fintype.card_fin] using hcard
    exact (Nat.not_lt_of_ge (hc.trans hbound)) hbig
  obtain ⟨c,hc,i,hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let p : MvPolynomial (Fin (r+1)) ℂ := ∑b,c b • BoxMonomials.affine b
  have hp : p≠0 := by
    intro he
    exact hi (Fintype.linearIndependent_iff.mp (BoxMonomials.affine_independent (r+1) t) c he i)
  refine ⟨p,hp,?_⟩
  have hzero : (∑b,c b • BoxMonomials.homogeneous j v b)∈F.leafPolynomialKernel P k := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (F.leafPolynomialKernel P k).mkQ (∑b,c b • BoxMonomials.homogeneous j v b)=0
    simpa only [map_sum,map_smul] using hc
  have hn : ∀ᶠ a in 𝓝 (P.chart (g.finite 1)).1,F.leafFrame P a j≠0 := by
    apply ((continuous_apply j).continuousAt.comp (F.leafFrame_continuousAt P hy)).eventually_ne
    simpa only [Function.comp_apply,leafFrame,Prod.mk.eta,P.chart.left_inv hy] using hj
  filter_upwards [hzero,hn] with a ha haj
  change MvPolynomial.eval (F.leafFrame P a) (↑(∑b,c b • BoxMonomials.homogeneous j v b))=0 at ha
  have he : MvPolynomial.eval (F.leafFrame P a) (↑(∑b,c b • BoxMonomials.homogeneous j v b))=
      (F.leafFrame P a j)^k *
        MvPolynomial.eval (fun i => F.leafFrame P a (v i)/F.leafFrame P a j) p := by
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,MvPolynomial.smul_eval,p,
      BoxMonomials.eval_homogeneous j v _ _ haj,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he] at ha
  exact (mul_eq_zero.mp ha).resolve_left (pow_ne_zero _ haj)

end SplitTangent.RationalCurveFrames

end

end OAI
