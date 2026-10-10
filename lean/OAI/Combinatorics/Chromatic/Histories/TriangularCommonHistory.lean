import Mathlib
import OAI.Combinatorics.Chromatic.Histories.CommonHistoryLeaves
import OAI.Combinatorics.Chromatic.Walls.TriangularAnchored

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma rootCone_dual_zero (N d:ℕ) (m:Extended (Vertex n (Cell n)))
    (hm:HasRootDegree (extendedRoots n) d (m-triangularBase N)) : m.2=0 := by
  obtain ⟨c,hc,he⟩:=hm
  have H:=congrArg Prod.snd he
  change (0:Lattice n (Cell n))=m.2-0 at H
  simpa using H.symm

def AnchoredLeaf {E:Type*} [AddCommGroup E] [Module ℝ E]
    (N:ℕ) (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E) (l:p.Leaf) : Prop :=
  ∃μ:Fin (n+1) →₀ ℕ,μ.degree=N ∧ (∀i:Fin n,μ i.succ≤μ i.castSucc) ∧
    p.leafExponent l=anchorExponent μ

def leafProfile {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : Fin (n+1) →₀ ℕ := l.property.choose
lemma leafProfile_degree {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : (leafProfile N p l).degree=N := l.property.choose_spec.1
lemma leafProfile_dominant {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : ∀i:Fin n,leafProfile N p l i.succ≤leafProfile N p l i.castSucc :=
  l.property.choose_spec.2.1
lemma leafProfile_exponent {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : p.leafExponent l.val=anchorExponent (leafProfile N p l) :=
  l.property.choose_spec.2.2

lemma triangularIncoming_anchorCoeff {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ≤μ i.castSucc) :
    polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression f) (anchorExponent μ)=
      (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff μ := by
  rw [←triangularExpression_anchorCoeff f μ]
  exact triangularPure_incoming f (fun a=>(μ a:ℤ)) (fun i=>Int.ofNat_le.mpr (hμ i))

lemma triangular_common_history (N d:ℕ) (r:Extended (Vertex n (Cell n)))
    (hr:HasRootDegree (extendedRoots n) d (r-triangularBase N)) :
    ∃p:LocalHistoryFormula (Extended (Vertex n (Cell n)))
      ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)),
      p.Positive (extendedOmega n) (extendedRoots n) extendedCast
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) ∧
      p.Bounded (extendedRoots n) (triangularBase N) d ∧
      ∀f:ElementaryExpr N, triangularExpression f r=
        ∑l:{l:p.Leaf // AnchoredLeaf N p l},
          p.leafWeight (extendedOmega n) (extendedRoots n) extendedCast
            (simpleTotalTransport (extendedOmega n) (extendedRoots n)) l.val *
          (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff (leafProfile N p l) := by
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  obtain ⟨p,hp,hb,he⟩:=polynomial_common_history (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible L
    (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (triangularBase N) (triangularBase_order N) d r hr
  refine ⟨p,hp,hb,?_⟩
  intro f
  rw [he (triangularExpression f) (fun m hm=>triangularSeed_in_rootCone f m (Finsupp.mem_support_iff.mpr hm))]
  have hz:∀l:p.Leaf,¬AnchoredLeaf N p l →
      polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
        (triangularExpression f) (p.leafExponent l)=0 := by
    intro l ha
    by_contra hh
    have hd:=rootCone_dual_zero N (p.leafDegree l) (p.leafExponent l) (p.leafBound _ _ _ hb l).2
    have hm:p.leafExponent l=includeVertices (p.leafExponent l).1:=Prod.ext rfl hd
    rw [hm] at hh
    obtain ⟨μ,hμ,hdom,hlabel⟩:=triangularExpression_anchorSupported f _ hh
    apply ha
    exact ⟨μ,hμ,hdom,hm.trans (congrArg includeVertices hlabel)⟩
  rw [←Fintype.sum_subtype_add_sum_subtype (AnchoredLeaf N p)]
  have hn:(∑l:{l:p.Leaf // ¬AnchoredLeaf N p l},
      p.leafWeight (extendedOmega n) (extendedRoots n) extendedCast
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) l.val *
      polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
        (triangularExpression f) (p.leafExponent l.val))=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l.val l.property,mul_zero]
  rw [hn,add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [leafProfile_exponent N p l]
  exact triangularIncoming_anchorCoeff f _ (leafProfile_dominant N p l)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
