import Mathlib
import OAI.Analysis.LaughlinGap.FastCoupling
import OAI.Analysis.LaughlinGap.RationalFourCertificate

namespace OAI

/-! Four Tables. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

def tableComparison (D : ℕ) (ε : ℚ)
    (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ := fun u v =>
  (if u=v then ((if 2*u.val+1=1 then 2 else 0)+ε)*copyNormalizationSq D (2*u.val+1) else 0) -
    copyNormalizationSq D (2*u.val+1) * Y u v * copyNormalizationSq D (2*v.val+1)

lemma fourCertificate_of_tables (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23)
    (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (hY : ∀ u v : Fin ((D+1)/2),
      (∑ a, (rows a).fourMatrixEval D (2*u.val+1) (2*v.val+1))=Y u v)
    (hZ : ∀ u v : Fin ((D+1)/2), rationalCreatedGram hD
      ((fourCopyEquiv D).symm u) ((fourCopyEquiv D).symm v)=Z u v)
    (hp : ((Z * tableComparison D ε Y * Z).map (algebraMap ℚ ℂ)).PosSemidef) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  apply fourCertificate_of_rational rows ε hD
  rw [← Matrix.posSemidef_submatrix_equiv (fourCopyEquiv D).symm]
  have hB : (rationalFourComparison rows ε D).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm = tableComparison D ε Y := by
    ext u v
    simp only [rationalFourComparison,Matrix.submatrix_apply,fourCopyEquiv_symm_val,
      Equiv.apply_eq_iff_eq,RationalRow.fourMatrix_eq_eval,hY,tableComparison]
    rfl
  have hG : (rationalCreatedGram hD).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm=Z := Matrix.ext hZ
  have he : (rationalFourCompression rows ε hD).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm = Z * tableComparison D ε Y * Z := by
    unfold rationalFourCompression
    rw [Matrix.submatrix_mul _ _ _ _ _ (fourCopyEquiv D).symm.bijective,
      Matrix.submatrix_mul _ _ _ _ _ (fourCopyEquiv D).symm.bijective,hG,hB]
  simpa only [Matrix.submatrix_map,he] using hp

lemma rationalCreatedGram_of_columns {D : ℕ} (hD : D ≤ 23) {K : ℕ}
    (keys : Fin K → Finset (Fin 25)) (cols : Matrix (Fin ((D+1)/2)) (Fin K) ℚ)
    (hk : fourKeys hD=Finset.univ.image keys) (hi : Function.Injective keys)
    (hc : ∀ u a, fourColumn hD (2*u.val+1) (keys a)=cols u a)
    (u v : Fin ((D+1)/2)) :
    rationalCreatedGram hD ((fourCopyEquiv D).symm u) ((fourCopyEquiv D).symm v) =
      ∑ a : Fin K, cols u a * cols v a / setFactorial (keys a) := by
  unfold rationalCreatedGram
  rw [hk,Finset.sum_image (fun _ _ _ _ h => hi h)]
  simp only [fourCopyEquiv_symm_val,hc]

end LaughlinGap.RealOccupation

end

end OAI
