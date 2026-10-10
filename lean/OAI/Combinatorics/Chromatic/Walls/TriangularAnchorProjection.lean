import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularMonomialCriterion
import OAI.Combinatorics.Chromatic.QuantumTorus.OrdinaryElementaryExpressions

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularAnchorProjectionRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) :=
  Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularAnchorProjectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularAnchorProjectionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularAnchorProjectionAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularAnchorProjectionSub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

def bridgeCut : Extended (Vertex n (Cell n)) →+ ℝ where
  toFun m:= -∑b:Cell n,(m.1 (.inr b):ℝ)
  map_zero':=by simp
  map_add' m r:=by simp [Finset.sum_add_distrib,add_comm]

lemma bridgeCut_anchor (a:Fin (n+1)) : bridgeCut (includeVertices (anchor a))=0 := by
  simp [bridgeCut,anchor]
lemma bridgeCut_bridge (b:Cell n) : bridgeCut (includeVertices (bridge b))= -1 := by
  simp [bridgeCut,bridge,Pi.single_apply]
lemma bridgeCut_pure (μ:Fin (n+1) → ℤ) : bridgeCut (includeVertices (pureAnchor μ))=0 := by
  simp only [pureAnchor,map_sum,map_zsmul,bridgeCut_anchor,zsmul_zero,Finset.sum_const_zero]

lemma triangularSeed_bridgeCut {N:ℕ} (f:ElementaryExpr N) :
    triangularExpression f∈supportedSubring LaurentRay.vUnit (extendedOmega n) (nonpositiveCone bridgeCut) := by
  intro m hm
  by_contra hn
  apply hm
  change -(∑b:Cell n,(m.1 (.inr b):ℝ)) ≤ 0
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro b _
  exact_mod_cast triangularSeed_nonneg f m (Finsupp.mem_support_iff.mpr hn) (.inr b)

lemma anchorExponent_single (a:Fin (n+1)) :
    anchorExponent (Finsupp.single a 1)=includeVertices (anchor a) := by
  apply Prod.ext
  · ext b
    cases b with
    | inl b=>simp [anchorExponent,pureAnchor_apply_anchor,anchor,Pi.single_apply,Finsupp.single_apply,eq_comm]
    | inr b=>simp [anchorExponent,pureAnchor_apply_bridge,anchor]
  · rfl

lemma anchorPolynomial_esymm (k:ℕ) :
    anchorPolynomial (MvPolynomial.esymm (Fin (n+1)) (LaurentSeries ℚ) k)=
      ∑s:Finset (Fin (n+1)),if s.card=k then
        Torus.X LaurentRay.vUnit (extendedOmega n) (∑a∈s,includeVertices (anchor a)) else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial,map_sum]
  have he:Finset.powersetCard k (Finset.univ:Finset (Fin (n+1)))=
      (Finset.univ:Finset (Finset (Fin (n+1)))).filter (fun s=>s.card=k):=by ext s; simp
  rw [he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · change anchorPolynomialAdd (MvPolynomial.monomial _ 1)=_
    rw [anchorPolynomial_monomial,map_sum]
    simp only [anchorExponent_single,Torus.X]
  · rfl

lemma independent_projection_pair (k:ℕ) (s:Finset (Fin (n+1))) (t:Finset (Cell n)) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut
      (independentTerm LaurentRay.vUnit (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) k (s.disjSum t))=
      if t=∅ then (if s.card=k then
        Torus.X LaurentRay.vUnit (extendedOmega n) (∑a∈s,includeVertices (anchor a)) else 0) else 0 := by
  have hsum:(∑x∈s.disjSum t,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)=
      (∑a∈s,includeVertices (anchor a))+(∑b∈t,includeVertices (bridge b)):=by
    exact sum_labels_disjSum _ _ s t
  have hcut:bridgeCut (∑x∈s.disjSum t,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)= -(t.card:ℝ):=by
    rw [hsum,map_add,map_sum,map_sum]
    simp only [bridgeCut_anchor,bridgeCut_bridge,Finset.sum_const_zero,zero_add,Finset.sum_const,nsmul_eq_mul,mul_neg,mul_one]
  by_cases ht:t=∅
  · subst t
    have hind:IsIndependent (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (s.disjSum ∅):=by
      intro x hx y hy
      obtain ⟨a,ha,rfl⟩:=Finset.mem_disjSum.mp hx |>.resolve_right (by simp)
      obtain ⟨b,hb,rfl⟩:=Finset.mem_disjSum.mp hy |>.resolve_right (by simp)
      change extendedOmega n (includeVertices (anchor a)) (includeVertices (anchor b))=0
      rw [extendedOmega_original]
      exact omega_anchors a b
    simp only [independentTerm,hind,true_and,Finset.card_disjSum,Finset.card_empty,add_zero,ite_true]
    split_ifs with hc
    · rw [setMonomial,Torus.X,zeroProject_monomial,show bridgeCut (∑x∈s.disjSum ∅,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)=0 by simpa using hcut,ite_eq_left rfl,hsum]
      simp only [Finset.sum_empty,add_zero,Torus.X]
    · exact map_zero _
  · rw [ite_eq_right ht,independentTerm]
    split_ifs
    · rw [setMonomial,Torus.X,zeroProject_monomial,ite_eq_right]
      rw [hcut]
      simpa only [neg_eq_zero,Nat.cast_eq_zero,Finset.card_eq_zero] using ht
    · exact map_zero _

lemma triangularAtom_projection (k:ℕ) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut (triangularExpression (.atom k))=
      anchorPolynomial (MvPolynomial.esymm (Fin (n+1)) (LaurentSeries ℚ) k) := by
  change zeroProject _ _ _ (independentElement _ _ (Sum.elim _ _) k)=_
  rw [independent_sum_decomposition]
  change zeroProject _ _ _ (∑t:Finset (Cell n),∑s:Finset (Fin (n+1)),
    independentTerm LaurentRay.vUnit (extendedOmega n)
      (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) k (s.disjSum t))=_
  rw [map_sum,anchorPolynomial_esymm]
  simp only [map_sum,independent_projection_pair]
  rw [Finset.sum_eq_single (∅:Finset (Cell n))]
  · simp only [ite_true]
  · intro t _ ht
    simp only [ite_eq_right ht,Finset.sum_const_zero]
  · simp

lemma triangularExpression_projection {N:ℕ} (f:ElementaryExpr N) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut (triangularExpression f)=
      anchorPolynomial (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)) := by
  induction f with
  | zero k=>exact (map_zero _).trans (map_zero _).symm
  | one=>exact (zeroProject_one _ _ _).trans (map_one _).symm
  | atom k=>exact triangularAtom_projection k
  | add f g hf hg=>simpa only [triangularExpression,ElementaryExpr.eval,ElementaryExpr.ordinary,map_add] using congrArg₂ (fun a b=>a+b) hf hg
  | neg f hf=>simpa only [triangularExpression,ElementaryExpr.eval,ElementaryExpr.ordinary,map_neg] using congrArg Neg.neg hf
  | mul f g hf hg=>
    change zeroProject _ _ _ (triangularExpression f*triangularExpression g)=anchorPolynomial (f.ordinary*g.ordinary)
    rw [zeroProject_mul_nonpositive _ _ _ _ _ (triangularSeed_bridgeCut f) (triangularSeed_bridgeCut g),hf,hg,map_mul]

lemma triangularExpression_anchorCoeff {N:ℕ} (f:ElementaryExpr N) (d:Fin (n+1) →₀ ℕ) :
    triangularExpression f (anchorExponent d)=(f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff d := by
  have H:=congrArg (fun t:Torus LaurentRay.vUnit (extendedOmega n)=>t (anchorExponent d)) (triangularExpression_projection (n:=n) f)
  rw [show (anchorPolynomial (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ))) (anchorExponent d)=
    (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff d from anchorPolynomial_coeff _ d] at H
  change ((triangularExpression f).filter (fun m=>bridgeCut m=0)) (anchorExponent d)=_ at H
  simpa only [Finsupp.filter_apply,show bridgeCut (anchorExponent d)=0 from bridgeCut_pure _,ite_true] using H
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
