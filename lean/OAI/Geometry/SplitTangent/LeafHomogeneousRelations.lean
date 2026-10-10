import Mathlib
import OAI.Geometry.SplitTangent.BoxMonomials
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafPolynomialGrowth

namespace OAI

/-! Leaf Homogeneous Relations. -/

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

include L in
theorem leaf_homogeneous_relation
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first (g.finite 1))+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃(k : ℕ) (Q : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k),
      Q∈F.leafPolynomialKernel P k ∧
      ∃p : MvPolynomial (Fin (Module.finrank ℂ (S.first (g.finite 1))+1)) ℂ,
        p≠0 ∧ ∀x : Fin (e.N+1) → ℂ,MvPolynomial.eval x D.val≠0 →
          MvPolynomial.eval x Q.val=(MvPolynomial.eval x D.val)^k*
            MvPolynomial.eval (fun i => MvPolynomial.eval x (H i).val/MvPolynomial.eval x D.val) p := by
  classical
  let r := Module.finrank ℂ (S.first (g.finite 1))
  let C := (F.degree+r+1)^r*(F.degree+1)
  obtain ⟨t,hbig⟩ := PolynomialGrowthArithmetic.box_exceeds C r
  let k := (r+1)*t
  obtain ⟨hfin,hbound⟩ := F.leaf_polynomial_growth L P hy ht hg k
  let := hfin
  let q : BoxMonomials.Box (r+1) t → F.LeafPolynomialGerms P k :=
    fun b => (F.leafPolynomialKernel P k).mkQ (BoxMonomials.homogeneousForms D H b)
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
  refine ⟨k,∑b,c b • BoxMonomials.homogeneousForms D H b,?_,p,hp,?_⟩
  · apply (Submodule.Quotient.mk_eq_zero _).mp
    change (F.leafPolynomialKernel P k).mkQ (∑b,c b • BoxMonomials.homogeneousForms D H b)=0
    simpa only [map_sum,map_smul] using hc
  · intro x hx
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,MvPolynomial.smul_eval,p,
      BoxMonomials.eval_homogeneousForms D H _ _ hx,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring

end SplitTangent.RationalCurveFrames

end

end OAI
