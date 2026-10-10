import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Regular.RegularSequence

namespace OAI

namespace PiExponentSiegel.W20

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

theorem regular_sequence_ideal_ne_top (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro htop
  apply hreg.top_ne_smul
  have hmul : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
    (Ideal.ofList rs).mul_top
  rw [hmul, htop]

theorem regular_sequence_term_not_isUnit (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    ¬ IsUnit rs[i] := by
  intro hunit
  apply regular_sequence_ideal_ne_top rs hreg
  exact (Ideal.ofList rs).eq_top_of_isUnit_mem
    (Ideal.subset_span (List.getElem_mem i.isLt)) hunit

theorem regular_sequence_term_ne_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) : rs[i] ≠ 0 := by
  let I : Ideal R := Ideal.ofList (rs.take i.val)
  have hle : I ≤ Ideal.ofList rs :=
    Ideal.span_mono (List.take_subset i.val rs)
  have hproper : I ≠ ⊤ := ne_top_of_le_ne_top
    (regular_sequence_ideal_ne_top rs hreg) hle
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have hmul : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) = I := I.mul_top
  rw [hmul] at hsmul
  intro hz
  have hz' : rs[i.val] = 0 := by simpa only [Fin.getElem_fin] using hz
  have hsmulzero : IsSMulRegular (R ⧸ I) (0 : R) := hz' ▸ hsmul
  exact IsSMulRegular.not_zero hsmulzero

end Ring

variable {k σ : Type*} [Field k]

theorem regular_homogeneous_degrees_pos
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    ∀ i, 0 < degrees i := by
  intro i
  by_contra hpos
  have hzero : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hhomzero : rs[i].IsHomogeneous 0 := by simpa only [hzero] using hhom i
  have hdegzero : (rs[i]).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hhomzero
  have hconstant : rs[i] = MvPolynomial.C ((rs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegzero
  have hcoeff : (rs[i]).coeff 0 ≠ 0 := by
    intro hz
    apply regular_sequence_term_ne_zero rs hreg i
    rw [hconstant, hz, map_zero]
  apply regular_sequence_term_not_isUnit rs hreg i
  rw [hconstant]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

theorem regular_homogeneous_degree_product_ne_zero
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    (∏ i : Fin rs.length, degrees i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Nat.ne_of_gt (regular_homogeneous_degrees_pos rs degrees hhom hreg i)

end PiExponentSiegel.W20

end OAI
