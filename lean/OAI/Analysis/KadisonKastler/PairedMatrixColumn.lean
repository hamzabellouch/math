import OAI.Analysis.KadisonKastler.PairedMatrixProjection

namespace OAI

/-! # The partial isometry from a matrix corner to central vectors

This is the algebraic corner map in Haagerup, Acta Math.158(1987),
Lemma3.5. Its initial projection is the matching minimal corner; its
final projection is the finite-matrix central-vector projection.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E F : MatrixUnitSystem ι (H →L[ℂ] H))
  (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

include hc in
omit [Nonempty ι] in
private theorem matchingEntry_mul (i j k l : ι) :
    (E.entry i j * F.entry i j) * (E.entry k l * F.entry k l) =
      if j = k then E.entry i l * F.entry i l else 0 := by
  calc
    _ = (E.entry i j * E.entry k l) * (F.entry i j * F.entry k l) := by
      rw [mul_assoc,← mul_assoc (F.entry i j),← (hc k l i j).eq]
      simp only [mul_assoc]
    _ = _ := by rw [E.mul_entry,F.mul_entry]; split_ifs <;> simp

include hc in
omit [Nonempty ι] in
private theorem matchingEntry_star (i j : ι) :
    star (E.entry i j * F.entry i j) = E.entry j i * F.entry j i := by
  rw [star_mul,E.star_entry,F.star_entry,← (hc j i j i).eq]

def pairedMatrixColumn (o : ι) : H →L[ℂ] H :=
  Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ∑ i, E.entry i o * F.entry i o

omit [DecidableEq ι] [Nonempty ι] in
private theorem pairedMatrixColumn_scalar_sq :
    (Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) *
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹)) = (Fintype.card ι : ℂ)⁻¹ := by
  have he : (Real.sqrt (Fintype.card ι))⁻¹ * (Real.sqrt (Fintype.card ι))⁻¹ =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [← mul_inv_rev,← pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← Complex.ofReal_mul,he,Complex.ofReal_inv,Complex.ofReal_natCast]

include hc in
omit [Nonempty ι] in
theorem pairedMatrixColumn_star (o : ι) :
    star (pairedMatrixColumn E F o) =
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
        ∑ i, E.entry o i * F.entry o i := by
  have hs : star (Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹)) =
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) :=
    Complex.conj_ofReal _
  simp only [pairedMatrixColumn,star_smul,star_sum]
  rw [hs]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => matchingEntry_star E F hc i o)

include hc in
theorem pairedMatrixColumn_initial (o : ι) :
    star (pairedMatrixColumn E F o) * pairedMatrixColumn E F o =
      E.entry o o * F.entry o o := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [pairedMatrixColumn_star E F hc]
  simp only [pairedMatrixColumn,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [pairedMatrixColumn_scalar_sq]
  simp only [Finset.sum_mul,Finset.mul_sum,matchingEntry_mul E F hc]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ hn,one_smul]

include hc in
omit [Nonempty ι] in
theorem pairedMatrixColumn_final (o : ι) :
    pairedMatrixColumn E F o * star (pairedMatrixColumn E F o) =
      pairedMatrixProjection E F := by
  rw [pairedMatrixColumn_star E F hc]
  simp only [pairedMatrixColumn,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [pairedMatrixColumn_scalar_sq]
  simp only [Finset.sum_mul,Finset.mul_sum,matchingEntry_mul E F hc,ite_true]
  rw [Finset.sum_comm]
  rfl

end

end KadisonKastler

end OAI
