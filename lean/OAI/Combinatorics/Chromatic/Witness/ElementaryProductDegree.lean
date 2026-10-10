import Mathlib
import OAI.Combinatorics.Chromatic.Witness.ProfilePartition
import OAI.Combinatorics.Chromatic.Walls.LaurentPolynomialEnergy

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma colCount_degree (s:B → Finset A) : (colCount s).degree=(rowCount s).degree := by
  simp only [colCount,map_sum,Finsupp.degree_single,Finset.sum_const,smul_eq_mul,mul_one]
  rw [Finsupp.degree_eq_sum]
  rfl

lemma elementary_product_coeff_zero {R:Type*} [CommSemiring R]
    (μ:A →₀ ℕ) (a:B →₀ ℕ) (h:a.degree≠μ.degree) :
    (∏i:A,MvPolynomial.esymm B R (μ i)).coeff a=0 := by
  rw [elementary_product_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  rw [ite_eq_right]
  rintro ⟨hr,hc⟩
  exact h (by rw [←hc,colCount_degree,hr])
end
end ElementaryPositivity.ElementaryMatrix

end
section
namespace ElementaryPositivity.Packets
open scoped BigOperators
variable {n:ℕ} {A R:Type*} [Fintype A] [LinearOrder A] [CommSemiring R]
omit [Fintype A] [LinearOrder A] in
lemma coloring_monomial (κ:Fin n → A) :
    (∏i:Fin n,MvPolynomial.X (κ i):MvPolynomial A R)=MvPolynomial.monomial (wordCount κ) 1 := by
  rw [wordCount,MvPolynomial.monomial_sum_one]
  rfl
end ElementaryPositivity.Packets
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)
lemma inversion_coefficient (r:ℕ) (a:Fin r →₀ ℕ) :
    (G.inversionChromatic r).coeff a=
    ∑κ:Fin n → Fin r,if G.Proper κ ∧ wordCount κ=a then
      (Polynomial.X^G.coloringInversions κ:Polynomial ℕ) else 0 := by
  unfold inversionChromatic
  rw [MvPolynomial.coeff_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro κ hκ
  by_cases hp:G.Proper κ
  · simp only [hp,ite_true,true_and,coloring_monomial,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  · simp [hp]
lemma inversion_coefficient_zero (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree≠n) :
    (G.inversionChromatic r).coeff a=0 := by
  rw [inversion_coefficient]
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨_,he⟩
  exact ha (he ▸ wordCount_degree κ)
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end
section
namespace ElementaryPositivity.TriangularDynamics
open Packets WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma decorated_polynomial_expansion (r:ℕ) : G.inversionChromatic r=
    ∑d:DecoratedLeaf G,MvPolynomial.C (Polynomial.X^leafEnergy G d)*
      MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (leafPartition G d) := by
  apply MvPolynomial.ext
  intro a
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,leafPartition,esymmPart_profile]
  by_cases ha:a.degree=n
  · apply LaurentPositive.centered_injective G.edgeCount
    rw [G.inversion_coefficient,LaurentPositive.centered_sum,LaurentPositive.centered_sum]
    simp only [LaurentPositive.centered_mul,LaurentPositive.map_elementary_coeff,
      LaurentPositive.centered_X_pow]
    have he:∀κ:Fin n → Fin r, wordCount κ=a ↔ ∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c:=by
      intro κ
      constructor
      · intro h c; rw [←h,wordCount_apply]
      · intro h; ext c; rw [wordCount_apply]; exact h c
    simp only [apply_ite,LaurentPositive.centered_X_pow,LaurentPositive.centered_zero,he]
    exact decorated_coefficient G r a ha
  · rw [G.inversion_coefficient_zero r a ha]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [ElementaryMatrix.elementary_product_coeff_zero _ _ (by simpa only [historyProfile_degree] using ha),mul_zero]

lemma admissible_polynomial_expansion (r:ℕ) : G.inversionChromatic r=
    ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
      MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (admissiblePartition G w) := by
  rw [decorated_polynomial_expansion,←Equiv.sum_comp (admissibleHistoryEquiv G)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [admissibleHistoryEquiv_energy]
  rfl
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open scoped BigOperators
variable {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n)

def ofAdmissibleWitness
    (lam:{w:Equiv.Perm (Fin n) // G.Admissible w} → Nat.Partition n)
    (hexp:∀r:ℕ,G.inversionChromatic r=
      ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
        MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
          MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (lam w)) : G.PermutationWitness where
  theta σ:=lam (G.reversalEquiv σ)
  expansion r:=by
    rw [←G.reflect_inversionChromatic r,hexp r,map_sum]
    rw [←Equiv.sum_comp G.reversalEquiv]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [CoefficientReflection.reflect_C_X_pow_mul_esymmPart _ _ _ (G.graphInversions_le_edges _)]
    congr 2
    congr 1
    change G.edgeCount-G.graphInversions (reversePerm σ.val)=G.graphInversions σ.val
    have H:=G.graphInversions_add_reverse σ.val
    omega
end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
