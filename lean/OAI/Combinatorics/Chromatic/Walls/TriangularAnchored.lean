import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularMonomialProducer
import OAI.Combinatorics.Chromatic.QuantumTorus.ExpressionAdditiveOperations

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}

lemma triangularIncoming_zero (N : ℕ) (m : Lattice n (Cell n)) :
    triangularIncoming (.zero N) m = 0 := by
  simp [triangularIncoming,triangularExpression,ElementaryExpr.eval,polynomialSectionIncoming,
    polynomialSectionCoefficient,actualPolynomialAdjointCoefficient]
lemma triangularIncoming_add {N : ℕ} (f g : ElementaryExpr N) (m : Lattice n (Cell n)) :
    triangularIncoming (.add f g) m = triangularIncoming f m + triangularIncoming g m :=
  actualPolynomialAdjointCoefficient_add _ _ _ _ _ _
lemma triangularIncoming_neg {N : ℕ} (f : ElementaryExpr N) (m : Lattice n (Cell n)) :
    triangularIncoming (.neg f) m = -triangularIncoming f m := by
  have H := triangularIncoming_add f (.neg f) m
  have hz : triangularIncoming (.add f (.neg f)) m = 0 := by
    change actualPolynomialAdjointCoefficient _ _ _ (triangularExpression f + -triangularExpression f) _ = 0
    rw [add_neg_cancel]
    simp [actualPolynomialAdjointCoefficient]
  rw [hz] at H
  exact eq_neg_of_add_eq_zero_right H.symm

def AnchorSupported {N:ℕ} (f : ElementaryExpr N) : Prop :=
  ∀ m : Lattice n (Cell n), triangularIncoming f m ≠ 0 →
    ∃ μ : Fin (n+1) →₀ ℕ, μ.degree = N ∧
      (∀ i : Fin n, μ i.succ ≤ μ i.castSucc) ∧ m = natAnchor (fun a => μ a)

lemma AnchorSupported.zero (N:ℕ) : AnchorSupported (n:=n) (.zero N) := by
  intro m h; exact (h (triangularIncoming_zero N m)).elim
lemma AnchorSupported.add {N:ℕ} {f g:ElementaryExpr N}
    (hf:AnchorSupported (n:=n) f) (hg:AnchorSupported (n:=n) g) :
    AnchorSupported (n:=n) (.add f g) := by
  intro m hm
  rw [triangularIncoming_add] at hm
  by_cases h:triangularIncoming f m=0
  · rw [h,zero_add] at hm; exact hg m hm
  · exact hf m h
lemma AnchorSupported.neg {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) :
    AnchorSupported (n:=n) (.neg f) := by
  intro m hm
  rw [triangularIncoming_neg] at hm
  exact hf m (fun h=>hm (by rw [h,neg_zero]))
lemma AnchorSupported.nscale {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) (k:ℕ) :
    AnchorSupported (n:=n) (f.nscale k) := by
  induction k with
  | zero=>exact AnchorSupported.zero N
  | succ k ih=>exact ih.add hf
lemma AnchorSupported.zscale {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) (z:ℤ) :
    AnchorSupported (n:=n) (f.zscale z) := by
  cases z with
  | ofNat k=>exact hf.nscale k
  | negSucc k=>exact (hf.nscale (k+1)).neg

lemma monomial_producer_supported (μ : Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n, μ i.succ ≤ μ i.castSucc) :
    ∃ f:ElementaryExpr μ.degree,
      f.ordinary=(OrbitMonomial.polynomial μ : MvPolynomial (Fin (n+1)) ℤ) ∧
      AnchorSupported (n:=n) f := by
  obtain ⟨f,hf,d,hd,he⟩:=triangularMonomial_producer μ hμ
  refine ⟨f,hf,?_⟩
  intro m hm
  obtain ⟨c,hc⟩:=triangularIncoming_in_rootCone f m hm
  let k:=∑i,c i
  have hk:HasRootDegree (extendedRoots n) k (includeVertices m-triangularBase μ.degree):=by
    refine ⟨c,rfl,?_⟩
    change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=includeVertices m-includeVertices ((μ.degree:ℤ) • anchor 0)
    rw [hc,map_add,add_sub_cancel_left]
  have H := polynomialInitial_incoming (extendedOmega n) extendedOmega_self (extendedRoots n)
    (extendedCoord n) extendedCoord_roots (triangularBase μ.degree) (triangularBase_order μ.degree)
    (triangularExpression f) (by intro a ha; exact triangularSeed_in_rootCone f a (Finsupp.mem_support_iff.mpr ha)) k _ hk
  rw [he,coneThetaInitial_prescription _ _ _ _ _ _ hd] at H
  have hlabel:includeVertices m=anchorExponent μ:=by
    by_contra hh
    have hz:coneDelta (extendedOmega n) d (anchorExponent μ) k (includeVertices m)=0:=by
      unfold coneDelta
      split_ifs
      · exact Finsupp.single_eq_of_ne hh
      · rfl
    exact hm (H.symm.trans hz)
  exact ⟨μ,rfl,hμ,congrArg Prod.fst hlabel⟩

lemma triangularExpression_anchorSupported {N:ℕ} (f:ElementaryExpr N) : AnchorSupported (n:=n) f := by
  let p:MvPolynomial (Fin (n+1)) ℤ:=f.ordinary
  let s:=p.support.filter (fun μ=>∀i:Fin n,μ i.succ ≤ μ i.castSucc)
  have ht:∀μ∈s,∃g:ElementaryExpr N,
      g.ordinary=MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ ∧ AnchorSupported (n:=n) g:=by
    intro μ hμ
    obtain ⟨hmem,hdom⟩:=Finset.mem_filter.mp hμ
    have hdeg:μ.degree=N:=by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hmem) (f.ordinary_homogeneous.coeff_eq_zero h)
    obtain ⟨g,hg,hs⟩:=monomial_producer_supported μ hdom
    let g':ElementaryExpr N:=hdeg ▸ g
    have ho:g'.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ):=by
      rw [ElementaryExpr.ordinary_cast]; exact hg
    have hs':AnchorSupported (n:=n) g':=by
      subst N; exact hs
    refine ⟨g'.zscale (p.coeff μ),?_,hs'.zscale _⟩
    rw [ElementaryExpr.ordinary_zscale,ho,zsmul_eq_mul]
    congr 1
  have hw:∀t:Finset (Fin (n+1) →₀ ℕ),t⊆s → ∃g:ElementaryExpr N,
      g.ordinary=∑μ∈t,MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ ∧ AnchorSupported (n:=n) g:=by
    intro t
    induction t using Finset.induction with
    | empty=>intro _; exact ⟨.zero N,by simp [ElementaryExpr.ordinary],AnchorSupported.zero N⟩
    | @insert μ t hμ ih=>
      intro h
      obtain ⟨g,hg,hs⟩:=ht μ (h (Finset.mem_insert_self _ _))
      obtain ⟨g',hg',hs'⟩:=ih (fun a ha=>h (Finset.mem_insert_of_mem ha))
      refine ⟨.add g g',?_,hs.add hs'⟩
      change g.ordinary+g'.ordinary=_
      rw [hg,hg',Finset.sum_insert hμ]
  obtain ⟨g,hg,hs⟩:=hw s (fun _=>id)
  have hp:p=∑μ∈s,MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ:=
    OrbitMonomial.symmetric_orbit_decomposition p f.ordinary_symmetric
  have he:triangularExpression (n:=n) f=triangularExpression g:=
    triangularExpression_ordinary_equal f g (hp.trans hg.symm)
  intro m hm
  have hi:triangularIncoming f m=triangularIncoming g m:=by unfold triangularIncoming; rw [he]
  rw [hi] at hm
  exact hs m hm
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
