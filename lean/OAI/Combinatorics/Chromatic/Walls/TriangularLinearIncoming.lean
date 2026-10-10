import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootCoefficientLocality
import OAI.Combinatorics.Chromatic.Walls.TriangularIncoming
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentElement

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularLinear_sum : triangularExpression (n:=n) (.atom 1)=
    ∑a:Vertex n (Cell n),Torus.X LaurentRay.vUnit (extendedOmega n)
      (includeVertices (Pi.single a (1:ℤ))) := by
  unfold triangularExpression ElementaryExpr.eval
  rw [independentElement_one _ _ extendedOmega_self]
  apply Finset.sum_congr rfl
  intro a _
  rw [initial_vertexDisplay]

lemma triangularLinear_support (m:Extended (Vertex n (Cell n)))
    (hm:(triangularExpression (.atom 1)) m≠0) :
    ∃a:Vertex n (Cell n),m=includeVertices (Pi.single a (1:ℤ)) := by
  rw [triangularLinear_sum,Finsupp.finsetSum_apply] at hm
  obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨a,?_⟩
  by_contra hh
  exact ha (Finsupp.single_eq_of_ne hh)

lemma vertex_single_injective : Function.Injective (fun a:Vertex n (Cell n)=>
    includeVertices (Pi.single a (1:ℤ))) := by
  intro a b hab
  by_contra h
  have H:=congrArg (fun m:Extended (Vertex n (Cell n))=>m.1 a) hab
  change (Pi.single a (1:ℤ):Lattice n (Cell n)) a=(Pi.single b (1:ℤ):Lattice n (Cell n)) a at H
  simp only [Pi.single_eq_same,Pi.single_eq_of_ne h] at H
  omega

lemma triangularLinear_vertex (a:Vertex n (Cell n)) :
    triangularExpression (.atom 1) (includeVertices (Pi.single a (1:ℤ)))=1 := by
  rw [triangularLinear_sum,Finsupp.finsetSum_apply,Finset.sum_eq_single a]
  · simp [Torus.X,Torus.monomial]
  · intro b _ hba
    apply Finsupp.single_eq_of_ne
    intro hh
    exact hba (vertex_single_injective hh.symm)
  · simp

lemma triangularLinear_locality (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
    triangularIncoming (.atom 1) m=triangularExpression (.atom 1) (includeVertices m) := by
  obtain ⟨c,hc⟩:=triangularIncoming_in_rootCone (.atom 1) m hm
  simp only [Nat.cast_one,one_smul] at hc
  obtain ⟨hK,hxi,_⟩:=triangularExpression_stationary (.atom 1) m hm
  exact actualPolynomialAdjoint_locality (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots
    (rootSectionChart (extendedOmega n) (extendedRoots n) (incomingCovector (extendedOmega n) (includeVertices m)))
    (includeVertices (anchor 0)) (includeVertices m) c (by rw [hc,map_add]; rfl)
    (triangularExpression (.atom 1)) (by
      intro b hb
      simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) b hb)
    (by intro g hg
        rw [extendedRoot_eq,extendedOmega_original]
        exact positive_gap_target_zero (fun i=>(c i:ℤ)) m (fun _=>Int.natCast_nonneg _) hc hK hxi g
          (by exact_mod_cast hg))

lemma stationary_vertex_initial (a:Vertex n (Cell n))
    (hK:∀i,levelTotal cellLevel i (Pi.single a (1:ℤ))=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (Pi.single a (1:ℤ))) :
    a=Sum.inl (0:Fin (n+1)) := by
  cases a with
  | inr b =>
    have H:=hK b.1
    change levelTotal cellLevel b.1 (bridge b)=0 at H
    simp only [levelTotal_bridge,cellLevel,ite_true] at H
    contradiction
  | inl a =>
    congr 1
    by_contra ha
    have ha0:0 < a.val:=by
      have hh:a.val≠0:=by intro H; exact ha (Fin.ext H)
      omega
    let i:Fin n:=⟨a.val-1,by have := a.isLt; omega⟩
    let b:Cell n:=⟨i,⟨0,by omega⟩⟩
    have H:=hxi b
    change 0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (anchor a) at H
    rw [eventRoot_anchor] at H
    have he:a=b.1.succ:=by apply Fin.ext; dsimp [b,i]; omega
    have hn:a≠b.1.castSucc:=by intro hh; have := congrArg Fin.val hh; dsimp [b,i] at this; omega
    rw [ite_eq_left he,ite_eq_right hn] at H
    omega

lemma triangularLinear_onlyIncoming (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
    m=anchor 0 := by
  have H:=triangularLinear_locality m hm
  rw [H] at hm
  obtain ⟨a,ha⟩:=triangularLinear_support (includeVertices m) hm
  have he:m=Pi.single a (1:ℤ):=congrArg Prod.fst ha
  obtain ⟨hK,hxi,_⟩:=triangularExpression_stationary (.atom 1) m (by rw [H]; exact hm)
  rw [he] at hK hxi
  rw [he,stationary_vertex_initial a hK hxi]
  rfl
lemma triangularLinear_anchorIncoming : triangularIncoming (n:=n) (.atom 1) (anchor 0)=1 := by
  have H:=actualPolynomialAdjoint_locality (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots
    (rootSectionChart (extendedOmega n) (extendedRoots n) (incomingCovector (extendedOmega n) (includeVertices (anchor 0))))
    (includeVertices (anchor 0)) (includeVertices (anchor 0)) (fun _=>0) (by
      change _ = _ + extendedRoots n 0
      rw [map_zero,add_zero])
    (triangularExpression (.atom 1)) (by
      intro b hb
      simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) b hb)
    (by intro g hg; omega)
  change triangularIncoming (.atom 1) (anchor 0)=_ at H
  rw [H]
  exact triangularLinear_vertex (.inl 0)

lemma triangularLinear_incoming (m:Lattice n (Cell n)) :
    triangularIncoming (.atom 1) m=if m=anchor 0 then 1 else 0 := by
  by_cases hm:m=anchor 0
  · rw [hm,ite_eq_left rfl,triangularLinear_anchorIncoming]
  · rw [ite_eq_right hm]
    by_contra hn
    exact hm (triangularLinear_onlyIncoming m hn)

lemma triangularIncoming_dual_zero {N:ℕ} (f:ElementaryExpr N) (m:Extended (Vertex n (Cell n)))
    (hm:polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression f) m≠0) : m.2=0 := by
  obtain ⟨b,hb,d,c,_,he⟩:=polynomialSection_support (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) (incomingCovector (extendedOmega n) m)
    (triangularExpression f) m hm
  have H:=congrArg Prod.snd he
  change 0=m.2-b.2 at H
  rw [triangularSeed_dual_zero f b hb,sub_zero] at H
  exact H.symm

lemma triangularLinear_fullIncoming (m:Extended (Vertex n (Cell n))) :
    polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression (.atom 1)) m=if m=includeVertices (anchor 0) then 1 else 0 := by
  by_cases hd:m.2=0
  · have he:m=includeVertices m.1:=Prod.ext rfl hd
    rw [he]
    change triangularIncoming (.atom 1) m.1=_
    rw [triangularLinear_incoming]
    congr 1
    apply propext
    constructor
    · intro hh; rw [hh]
    · exact fun hh=>congrArg Prod.fst hh
  · have hn:m≠includeVertices (anchor 0):=by intro hh; exact hd (congrArg Prod.snd hh)
    rw [ite_eq_right hn]
    by_contra hz
    exact hd (triangularIncoming_dual_zero (.atom 1) m hz)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
