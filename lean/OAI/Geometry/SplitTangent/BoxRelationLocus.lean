import Mathlib
import OAI.Geometry.SplitTangent.BoxMonomials
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.HolomorphicCommonZeros
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PolynomialRelationLocus
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafClosureRelations

namespace OAI

/-! Box Relation Locus. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace BoxMonomials

def indexedForms {σ : Type*} {m : ℕ}
    (D : MvPolynomial.homogeneousSubmodule σ ℂ 1)
    (H : Fin m → MvPolynomial.homogeneousSubmodule σ ℂ 1) (t : ℕ) :
    Fin (Fintype.card (Box m t)) → MvPolynomial.homogeneousSubmodule σ ℂ (m*t) :=
  fun j => homogeneousForms D H ((Fintype.equivFin (Box m t)).symm j)

def indexedAffine {m t : ℕ} :
    Fin (Fintype.card (Box m t)) → MvPolynomial (Fin m) ℂ :=
  fun j => affine ((Fintype.equivFin (Box m t)).symm j)

lemma indexedAffine_independent (m t : ℕ) : LinearIndependent ℂ (@indexedAffine m t) :=
  (affine_independent m t).comp _ (Fintype.equivFin (Box m t)).symm.injective

lemma indexedForms_eval {σ : Type*} {m t : ℕ}
    (D : MvPolynomial.homogeneousSubmodule σ ℂ 1)
    (H : Fin m → MvPolynomial.homogeneousSubmodule σ ℂ 1)
    (j : Fin (Fintype.card (Box m t))) (v : σ → ℂ) (hv : MvPolynomial.eval v D.val≠0) :
    MvPolynomial.eval v (indexedForms D H t j).val=(MvPolynomial.eval v D.val)^(m*t)*
      MvPolynomial.eval (fun i => MvPolynomial.eval v (H i).val/MvPolynomial.eval v D.val)
        (indexedAffine j) := eval_homogeneousForms D H _ v hv

end BoxMonomials
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X) {r : ℕ}
  (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
  (H : Fin (r+1) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)

def boxRelationLocus (t : ℕ) : Set X.Carrier :=
  L.relationLocus e (BoxMonomials.indexedForms D H t)

lemma boxRelationLocus_locally_holomorphic (t : ℕ) :
    LocallyHolomorphicCommonZeros X (L.boxRelationLocus e D H t) :=
  L.relationLocus_locally_holomorphic e _

lemma boxRelationLocus_affine {t : ℕ} {x : X.Carrier}
    (hx : x∈L.boxRelationLocus e D H t) :
    ∃p : MvPolynomial (Fin (r+1)) ℂ,p≠0 ∧
      ∀z∈closure (L.leaf x),MvPolynomial.eval (e.map z).rep D.val≠0 →
        MvPolynomial.eval (fun i => MvPolynomial.eval (e.map z).rep (H i).val /
          MvPolynomial.eval (e.map z).rep D.val) p=0 := by
  classical
  obtain ⟨c,hc,hzero⟩ := hx
  let p : MvPolynomial (Fin (r+1)) ℂ := ∑j,c j • BoxMonomials.indexedAffine j
  refine ⟨p,?_,?_⟩
  · intro he
    apply hc
    funext j
    exact Fintype.linearIndependent_iff.mp (BoxMonomials.indexedAffine_independent (r+1) t) c he j
  · intro z hz hD
    have hh : MvPolynomial.eval (e.map z).rep
        (relationPolynomial e (BoxMonomials.indexedForms D H t) c).val=0 := hzero hz
    rw [relation_eval] at hh
    simp only [BoxMonomials.indexedForms_eval D H _ _ hD,mul_assoc,←Finset.mul_sum] at hh
    apply (mul_eq_zero_iff_left (pow_ne_zero _ hD)).mp
    convert hh using 1
    simp only [p,map_sum,MvPolynomial.smul_eval]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

end SplitTangent.LeafJetAtlas
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S)

include F in
lemma exists_boxRelationLocus (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first (g.finite 1))+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃t,g.finite 1∈L.boxRelationLocus e D H t := by
  classical
  let P := L.chart (g.finite 1)
  have hy : g.finite 1∈P.chart.source := L.mem_source _
  let r := Module.finrank ℂ (S.first (g.finite 1))
  let C := (F.degree+r+1)^r*(F.degree+1)
  obtain ⟨t,hbig⟩ := PolynomialGrowthArithmetic.box_exceeds C r
  let k := (r+1)*t
  obtain ⟨hfin,hbound⟩ := F.leaf_polynomial_growth L P hy ht hg k
  let := hfin
  let q : Fin (Fintype.card (BoxMonomials.Box (r+1) t)) → F.LeafPolynomialGerms P k :=
    fun j => (F.leafPolynomialKernel P k).mkQ (BoxMonomials.indexedForms D H t j)
  have hnot : ¬LinearIndependent ℂ q := by
    intro hlin
    have hc : (t+1)^(r+1) ≤ Module.finrank ℂ (F.LeafPolynomialGerms P k) := by
      simpa only [BoxMonomials.Box,Fintype.card_fun,Fintype.card_fin] using hlin.fintype_card_le_finrank
    exact (Nat.not_lt_of_ge (hc.trans hbound)) hbig
  obtain ⟨c,hc,j,hj⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨t,c,?_,?_⟩
  · intro he
    exact hj (congrFun he j)
  · apply F.polynomialKernel_closure_zero L P hy
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (F.leafPolynomialKernel P k).mkQ (∑j,c j • BoxMonomials.indexedForms D H t j)=0
    simpa only [map_sum,map_smul] using hc

end SplitTangent.RationalCurveFrames

end

end OAI
