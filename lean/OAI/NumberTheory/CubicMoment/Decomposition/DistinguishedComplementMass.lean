import OAI.NumberTheory.CubicMoment.Estimates.ComplementAbsoluteCollection
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeVariation

namespace OAI

/-! The complementary tuple mass for the literal smooth distinguished
weights. Their rough support is proved from the detector difference. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedRadialWeight_eq_primeWeight (W : ℝ → ℂ) (w z : ℝ) (p : Eisenstein) :
    distinguishedRadialWeight W w z (norm p) =
      W (norm p)*distinguishedPrimeWeight primeDetectorCutoff w z p := by
  simp only [distinguishedRadialWeight,distinguishedPrimeWeight,Complex.ofReal_sub]

lemma distinguishedRadialWeight_prime_rough (W : ℝ → ℂ) {w z : ℝ}
    (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein} (hp : primaryPrime p)
    (hne : distinguishedRadialWeight W w z (norm p) ≠ 0) : w < norm p := by
  rw [distinguishedRadialWeight_eq_primeWeight] at hne
  exact (distinguishedPrimeWeight_support
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
    hw hwz (norm_pos_of_ne_zero hp.2.ne_zero) (mul_ne_zero_iff.mp hne).2).1

theorem distinguished_complement_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → ℝ → ℂ) (hW : ∀ j x, ‖W j x‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w z : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w) (hwz : w ≤ z)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i,
        ‖distinguishedRadialWeight (W j) w z (norm (t.1 j))‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply complement_absolute_tuple_mass S hS i
    (fun j p => distinguishedRadialWeight (W j) w z (norm p)) ?_ D hD hY hw ?_ hsize
  · intro j p hp
    rw [distinguishedRadialWeight,norm_mul]
    exact (mul_le_mul (hW j (norm p)) (detector_difference_norm w z (norm p))
      (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro j _ p hp hne
    exact (distinguishedRadialWeight_prime_rough (W j)
      (zero_lt_one.trans_le hw) hwz (hS j p hp) hne).le

end CubicFirstMoment

end

end OAI
