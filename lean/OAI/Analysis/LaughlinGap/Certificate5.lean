import Mathlib
import OAI.Analysis.LaughlinGap.CachedIntegerRows
import OAI.Analysis.LaughlinGap.FourTables
import OAI.Analysis.LaughlinGap.SumTable5

namespace OAI

/-! Certificate5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate5

def keys : Fin 1 → Finset (Fin 25) := ![{0,1,2,3}]
def fibers : Fin 1 → Finset (FourTerm 5) := ![{⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}]
def columns : Matrix (Fin 3) (Fin 1) ℚ := ![![24], ![-12], ![30]]
def Y : Matrix (Fin 3) (Fin 3) ℚ := ![![(-691918059642960348268939/469762048000000000000000), (143591010688663997337363/469762048000000000000000), (52406720056687264286281/187904819200000000000000)], ![(143591010688663997337363/469762048000000000000000), (-235485533349233444433063/1879048192000000000000000), (-32668914245365634602367/187904819200000000000000)], ![(52406720056687264286281/187904819200000000000000), (-32668914245365634602367/187904819200000000000000), (-382288393294507346704323/26843545600000000000000)]]
def Z : Matrix (Fin 3) (Fin 3) ℚ := ![![48, -24, 60], ![-24, 12, -30], ![60, -30, 75]]
def W : Matrix (Fin 3) (Fin 3) ℚ := ![![(62270372121978546147806337/15032385536000000000000000), (-41616573336114019844377/644245094400000000000000), (778609652914953277125223/15032385536000000000000000)], ![(-62270372121978546147806337/30064771072000000000000000), (41616573336114019844377/1288490188800000000000000), (-778609652914953277125223/30064771072000000000000000)], ![(62270372121978546147806337/12025908428800000000000000), (-41616573336114019844377/515396075520000000000000), (778609652914953277125223/12025908428800000000000000)]]
def M : Matrix (Fin 3) (Fin 3) ℚ := ![![(109249990074931830815538167/536870912000000000000000), (-109249990074931830815538167/1073741824000000000000000), (109249990074931830815538167/429496729600000000000000)], ![(-109249990074931830815538167/1073741824000000000000000), (109249990074931830815538167/2147483648000000000000000), (-109249990074931830815538167/858993459200000000000000)], ![(109249990074931830815538167/429496729600000000000000), (-109249990074931830815538167/858993459200000000000000), (109249990074931830815538167/343597383680000000000000)]]
def L : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 0, 0], ![(-1/2), 1, 0], ![(5/4), 0, 1]]
def diag : Fin 3 → ℚ := ![(109249990074931830815538167/536870912000000000000000), 0, 0]

lemma keys_checked : fourKeys (by omega : 5 ≤ 23) = Finset.univ.image keys := by decide +kernel
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma fibers_checked_0 : ∀ b : FourTerm 5,
    (fourTermLabels (by omega : 5 ≤ 23) b).toFinset=keys 0 ↔ b ∈ fibers 0 := by decide +kernel
lemma fibers_checked : ∀ a : Fin 1, ∀ b : FourTerm 5,
    (fourTermLabels (by omega : 5 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a
  fin_cases a
  · exact fibers_checked_0
lemma columns_checked_0 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(0 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(1 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(2 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 3, ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
lemma gram_checked_0 : ∀ v : Fin 3, (∑ a : Fin 1, columns (0 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 3, (∑ a : Fin 1, columns (1 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 3, (∑ a : Fin 1, columns (2 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 3, ∀ v : Fin 3, (∑ a : Fin 1, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
lemma rows_table_checked_0 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (0 : Fin 3) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (1 : Fin 3) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (2 : Fin 3) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 3, ∀ v : Fin 3, integerTableEval 5 SumTable5.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
lemma rows_checked (u v : Fin 3) : exactFourEval 5 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 5 SumTable5.sums SumTable5.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (0 : Fin 3) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (1 : Fin 3) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (2 : Fin 3) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 3, ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
lemma compression_checked_0 : ∀ v : Fin 3, (W * Z) (0 : Fin 3) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 3, (W * Z) (1 : Fin 3) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 3, (W * Z) (2 : Fin 3) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 3, ∀ v : Fin 3, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
lemma ldl_checked_0 : ∀ v : Fin 3, (∑ k : Fin 3, L (0 : Fin 3) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 3, (∑ k : Fin 3, L (1 : Fin 3) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 3, (∑ k : Fin 3, L (2 : Fin 3) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 3, ∀ v : Fin 3, (∑ k : Fin 3, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
lemma diag_checked : ∀ u : Fin 3, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 5 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 5 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 5 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 5 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 5 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate5
end LaughlinGap.RealOccupation

end

end OAI
