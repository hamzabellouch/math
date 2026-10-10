import Mathlib
import OAI.Analysis.LaughlinGap.ExactRows
import OAI.Analysis.LaughlinGap.RationalFourCertificate

namespace OAI

/-! Zero Certificates. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

lemma fourCertificate_of_empty_keys {ι : Type*} [Fintype ι] (rows : ι → RationalRow) (ε : ℚ)
    {D : ℕ} (hD : D ≤ 23) (hk : fourKeys hD=∅) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  apply fourCertificate_of_rational rows ε hD
  have hg : rationalCreatedGram hD=0 := by ext u v; simp [rationalCreatedGram,hk]
  simpa [rationalFourCompression,hg] using (Matrix.PosSemidef.zero : (0 : Matrix (FourCopy D) (FourCopy D) ℂ).PosSemidef)

lemma keys_empty_1 : fourKeys (by omega : 1 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_2 : fourKeys (by omega : 2 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_3 : fourKeys (by omega : 3 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_4 : fourKeys (by omega : 4 ≤ 23)=∅ := by decide +kernel

lemma certificate_1 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 1
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_1 using 1
  norm_num
lemma certificate_2 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 2
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_2 using 1
  norm_num
lemma certificate_3 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 3
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_3 using 1
  norm_num
lemma certificate_4 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 4
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_4 using 1
  norm_num
end LaughlinGap.RealOccupation

end

end OAI
