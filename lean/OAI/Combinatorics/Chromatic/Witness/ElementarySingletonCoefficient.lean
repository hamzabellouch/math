import Mathlib
import OAI.Combinatorics.Chromatic.Histories.GraphCommonHistory
import OAI.Combinatorics.Chromatic.Walls.LaurentFiniteDecorations

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A:Type*} [Fintype A] [DecidableEq A]
variable {R:Type*} [CommSemiring R]

def allOnes (n:ℕ) : Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun _=>1)
lemma allOnes_apply (n:ℕ) (i:Fin n) : allOnes n i=1:=rfl
lemma allOnes_degree (n:ℕ) : (allOnes n).degree=n := by
  change (allOnes n).sum (fun _ k=>k)=n
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl)]
  simp [allOnes_apply]

lemma singleton_coefficient {n:ℕ} (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    (∏i:A,MvPolynomial.esymm (Fin n) R (μ i)).coeff (allOnes n)=(μ.multinomial:R) := by
  rw [duality]
  simp only [allOnes_apply,MvPolynomial.esymm_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change μ.sum (fun _ k=>k)=n at hμ
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype,ite_eq_left hμ]

omit [Fintype A] [DecidableEq A] in
lemma profile_multinomial_pos (μ:A →₀ ℕ) : 0<μ.multinomial := Nat.multinomial_pos _ _
end
end ElementaryPositivity.ElementaryMatrix

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def historyDimension : ℕ:=(graph_common_history G).choose

def historySyntax : LocalHistoryFormula (Extended (Vertex (historyDimension G) (Cell (historyDimension G))))
    ((Vertex (historyDimension G) (Cell (historyDimension G)) → ℝ) ×
      (Vertex (historyDimension G) (Cell (historyDimension G)) → ℝ)) :=
  (graph_common_history G).choose_spec.choose

lemma historySyntax_positive : (historySyntax G).Positive
    (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G)) extendedCast
    (simpleTotalTransport (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G))) :=
  (graph_common_history G).choose_spec.choose_spec.1

abbrev HistoryLeaf := {l:(historySyntax G).Leaf // AnchoredLeaf n (historySyntax G) l}
def historyProfile (l:HistoryLeaf G) := leafProfile n (historySyntax G) l
lemma historyProfile_degree (l:HistoryLeaf G) : (historyProfile G l).degree=n :=
  leafProfile_degree n (historySyntax G) l
lemma historyProfile_dominant (l:HistoryLeaf G) :
    ∀i:Fin (historyDimension G),historyProfile G l i.succ≤historyProfile G l i.castSucc :=
  leafProfile_dominant n (historySyntax G) l

def historyWeight (l:HistoryLeaf G) : LaurentSeries ℚ:=
  (historySyntax G).leafWeight (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G))
    extendedCast (simpleTotalTransport (extendedOmega (historyDimension G))
      (extendedRoots (historyDimension G))) l.val
lemma historyWeight_positive (l:HistoryLeaf G) : LaurentPositive.Positive (historyWeight G l):=
  (historySyntax G).leafWeight_positive _ _ _ _ (historySyntax_positive G) l.val

lemma history_coefficient (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree=n) :
    (∑κ:Fin n → Fin r,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑l:HistoryLeaf G,historyWeight G l *
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G l i)).coeff a :=
  (graph_common_history G).choose_spec.choose_spec.2 r a ha

lemma history_singleton :
    (∑κ:Fin n → Fin n,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=1) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑l:HistoryLeaf G,historyWeight G l*(historyProfile G l).multinomial := by
  have he:=history_coefficient G n (ElementaryMatrix.allOnes n) (ElementaryMatrix.allOnes_degree n)
  simp only [ElementaryMatrix.allOnes_apply] at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro l hl
  rw [ElementaryMatrix.singleton_coefficient _ (historyProfile_degree G l)]

lemma historyWeight_support (l:HistoryLeaf G) (j:ℤ) (hj:(historyWeight G l).coeff j≠0) :
    ∃k:Fin (G.edgeCount+1),j=(G.edgeCount:ℤ)-2*(k.val:ℤ) := by
  apply LaurentPositive.support_of_positive_sum (historyWeight G) (historyWeight_positive G)
    (fun l=>(historyProfile G l).multinomial)
    (fun l=>ElementaryMatrix.profile_multinomial_pos _) _ _ l j hj
  intro j hn
  rw [←history_singleton G,HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro κ hκ
  split_ifs
  · rw [LaurentRay.vUnit_zpow]
    apply HahnSeries.coeff_single_of_ne
    intro he
    apply hn
    refine ⟨⟨G.coloringInversions κ,by
      have H:G.coloringInversions κ≤G.edgeCount:=Finset.card_le_card (Finset.filter_subset _ _)
      omega⟩,?_⟩
    change j=(G.edgeCount:ℤ)-2*(G.coloringInversions κ:ℤ)
    omega
  · rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
