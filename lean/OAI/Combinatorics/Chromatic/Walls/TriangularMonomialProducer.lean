import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularAnchorProjection
import OAI.Combinatorics.Chromatic.QuantumTorus.OrdinaryExpressionNaturality

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma orbitExpression_pureCoeff {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hf:f.ordinary= (OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ))
    (ν:Fin (n+1) → ℤ) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc) :
    triangularExpression f (includeVertices (pureAnchor ν))=if ν=(fun a=>(μ a:ℤ)) then 1 else 0 := by
  have hmap:f.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)):=by
    rw [←ElementaryExpr.ordinary_map f (Int.castRingHom (LaurentSeries ℚ)),hf,OrbitMonomial.polynomial_map]
  by_cases hnon:∀a,0 ≤ ν a
  · let d:Fin (n+1) →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun a=>(ν a).toNat)
    have hd:∀a,(d a:ℤ)=ν a:=fun a=>Int.toNat_of_nonneg (hnon a)
    have hdd:∀i:Fin n,d i.succ ≤ d i.castSucc:=by
      intro i
      exact Int.ofNat_le.mp (by simpa only [hd] using hν i)
    have he:includeVertices (pureAnchor ν)=anchorExponent d:=by
      change includeVertices (pureAnchor ν)=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
      rw [show (fun a=>(d a:ℤ))=ν from funext hd]
    rw [he,triangularExpression_anchorCoeff,hmap,OrbitMonomial.dominant_coeff μ d hμ hdd]
    have hh:d=μ ↔ ν=(fun a=>(μ a:ℤ)):=by
      constructor
      · intro h; funext a; rw [←hd a,h]
      · intro h; ext a; apply Int.ofNat_inj.mp; rw [hd,h]
    simp only [hh]
  · obtain ⟨a,ha⟩:=not_forall.mp hnon
    have he:ν≠(fun a=>(μ a:ℤ)):=by intro h; apply ha; rw [h]; exact Int.natCast_nonneg _
    rw [ite_eq_right he]
    by_contra hh
    have H:=triangularSeed_nonneg f _ (Finsupp.mem_support_iff.mpr hh) (.inl a)
    have H':0 ≤ pureAnchor ν (.inl a):=H
    exact ha (by simpa only [pureAnchor_apply_anchor] using H')

lemma natAnchor_rootDegree (μ:Fin (n+1) →₀ ℕ) :
    ∃d,HasRootDegree (extendedRoots n) d (anchorExponent μ-triangularBase μ.degree) := by
  have hpos:∀a,0 ≤ natAnchor (fun a=>μ a) a:=by
    intro a
    cases a <;> simp [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge]
  obtain ⟨d,c,hc,he⟩:=triangularVertex_rootDegree (natAnchor (fun a=>μ a)) hpos
  have hw:vertexWeight (natAnchor (fun a=>μ a))=(μ.degree:ℤ):=by
    rw [vertexWeight_apply,Fintype.sum_sum_type]
    simp only [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge,Finset.sum_const_zero,add_zero]
    rw [Finsupp.degree_eq_sum,Nat.cast_sum]
  refine ⟨d,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=anchorExponent μ-triangularBase μ.degree
  change forwardRoots (fun i=>(c i:ℤ))=natAnchor (fun a=>μ a)-vertexWeight (natAnchor (fun a=>μ a)) • anchor 0 at he
  rw [hw] at he
  rw [he,map_sub]
  rfl

lemma triangularMonomial_producer (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) :
    ∃f:ElementaryExpr μ.degree, f.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ) ∧
    ∃d,HasRootDegree (extendedRoots n) d (anchorExponent μ-triangularBase μ.degree) ∧
      polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)=
        coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
          (triangularBase μ.degree) d (anchorExponent μ) := by
  obtain ⟨f,hf⟩:=homogeneousExpression_representation (OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ)
    (OrbitMonomial.polynomial_symmetric μ) (OrbitMonomial.polynomial_homogeneous μ)
  obtain ⟨d,hd⟩:=natAnchor_rootDegree μ
  refine ⟨f,hf,d,hd,?_⟩
  exact triangularMonomial_initial f d (fun a=>μ a) (Finsupp.degree_eq_sum μ).symm hμ hd
    (orbitExpression_pureCoeff f μ hμ hf)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
