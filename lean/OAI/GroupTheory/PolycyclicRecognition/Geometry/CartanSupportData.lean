import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordTrace
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm

namespace OAI

/-! # Support data from the actual Cartan ideal

Every finite family of word bases in homogeneous lifts of an abelianization
basis gives balanced positive support data. The ambient adjoint action need
only be triangularizable, not diagonalizable.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {n m : ℕ} (T : TriangularAdjoint L n)
  (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
  (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))
  (bq : Basis (Fin m) ℝ (cartanRootAbelianization H))
  (hXq : ∀ i, (lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule.mkQ (X i) = bq i)
  (hgen : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)

/-- Support data for any finite collection of actual word bases. -/
def cartanSupportDatum {B J : Type*} [Fintype B] [Fintype J]
    (b : B → Basis J ℝ (cartanRootIdeal H))
    (words : B → J → FreeMagma (Fin m))
    (hwords : ∀ β j, evalBracketWord X (words β j) = b β j) :
    SupportDatum (HeightSpace T.character) (Fin m) B where
  weight i := cartanHeightWeight T H (χ i)
  multiplicity β i := ∑ j, bracketWordCount (words β j) i
  positive β := by
    let C := (lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) 1).toSubmodule
    apply positive_bracketWord_multiplicities C.mkQ _ X bq hXq (b β) (words β) (hwords β)
    intro x y
    apply (Submodule.Quotient.mk_eq_zero C).mpr
    change ⁅x, y⁆ ∈ lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (0 + 1)
    rw [lowerCentralSeries_succ, lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  balanced β := balanced_cartan_word_counts H X χ hX T (b β) (words β) (hwords β) hunimod
  separates := cartan_generator_weights_separate H T X χ hX hgen

include hunimod in
/-- In particular the support norm construction has genuine Lie algebra data
for every unimodular triangular adjoint action. -/
theorem exists_cartan_supportDatum :
    ∃ (m : ℕ) (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
      (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
      (words : Fin (finrank ℝ (cartanRootIdeal H)) → FreeMagma (Fin m))
      (D : SupportDatum (HeightSpace T.character) (Fin m) Unit),
      (∀ i, (χ i).IsNonZero ∧ (X i : L) ∈ rootSpace H (χ i)) ∧
      (∀ j, evalBracketWord X (words j) = b j) ∧
      (∀ i, D.weight i = cartanHeightWeight T H (χ i)) ∧
      (∀ i, D.multiplicity () i = ∑ j, bracketWordCount (words j) i) := by
  obtain ⟨m, X, χ, bq, hroot, hXq, hgen⟩ := exists_cartan_abelianization_generators H T
  obtain ⟨b, hb⟩ := exists_bracketWord_basis X hgen
  choose words hwords using hb
  let D := cartanSupportDatum H T X χ (fun i => (hroot i).2) bq hXq hgen hunimod
    (fun _ : Unit => b) (fun _ : Unit => words) (fun _ => hwords)
  exact ⟨m, X, χ, b, words, D, hroot, hwords, fun _ => rfl, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
