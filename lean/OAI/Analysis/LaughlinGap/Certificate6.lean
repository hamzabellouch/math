import Mathlib
import OAI.Analysis.LaughlinGap.Certificate5

namespace OAI

/-! Certificate6. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate6

def keys : Fin 1 → Finset (Fin 25) := ![{0,1,2,4}]
def fibers : Fin 1 → Finset (FourTerm 6) := ![{⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}]
def columns : Matrix (Fin 3) (Fin 1) ℚ := ![![0], ![0], ![0]]
def Y : Matrix (Fin 3) (Fin 3) ℚ := ![![(-796881811066228176743533/53687091200000000000000), (1382924902976753673/335544320000000000), (2719883565749028608244643/375809638400000000000000)], ![(1382924902976753673/335544320000000000), (-253735112474554296132261/134217728000000000000000), (-79579850485959191284893/46976204800000000000000)], ![(2719883565749028608244643/375809638400000000000000), (-79579850485959191284893/46976204800000000000000), (-692584773830283706404217/75161927680000000000000)]]
def Z : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]
def W : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]
def M : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]
def L : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
def diag : Fin 3 → ℚ := ![0, 0, 0]

lemma keys_checked : fourKeys (by omega : 6 ≤ 23) = Finset.univ.image keys := by decide +kernel
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma fibers_checked_0 : ∀ b : FourTerm 6,
    (fourTermLabels (by omega : 6 ≤ 23) b).toFinset=keys 0 ↔ b ∈ fibers 0 := by decide +kernel
lemma fibers_checked : ∀ a : Fin 1, ∀ b : FourTerm 6,
    (fourTermLabels (by omega : 6 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a
  fin_cases a
  · exact fibers_checked_0
lemma columns_checked_0 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(0 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(1 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(2 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 3, ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns u v := by
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
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 6 (by omega) := by
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 6 (by omega) by simpa using this
  apply fourCertificate_of_rational exactRows (1/200000) (by omega : 6 ≤ 23)
  have hg : rationalCreatedGram (by omega : 6 ≤ 23) = 0 := by
    ext u v
    obtain ⟨u,rfl⟩ := (fourCopyEquiv 6).symm.surjective u
    obtain ⟨v,rfl⟩ := (fourCopyEquiv 6).symm.surjective v
    rw [rationalCreatedGram_of_columns (by omega : 6 ≤ 23) keys columns keys_checked keys_injective]
    · have hz : Z=0 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
      simpa only [hz,Matrix.zero_apply] using gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 6 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  simpa [rationalFourCompression,hg] using (Matrix.PosSemidef.zero : (0 : Matrix (FourCopy 6) (FourCopy 6) ℂ).PosSemidef)
end Certificate6
end LaughlinGap.RealOccupation

end

end OAI
