import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayBounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayParameters

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveInverse (M d : ℕ) : ℤ := ZMod.cast ((M:ZMod d)⁻¹)

@[simp] theorem adaptiveInverse_cast (M d : ℕ) :
    (adaptiveInverse M d : ZMod d) = (M:ZMod d)⁻¹ := ZMod.intCast_zmod_cast _

def adaptiveArraySupport (L Z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (Z^14)).filter (fun s => Squarefree s ∧ s.Coprime L)

def adaptiveContinuousArray (L Z M h P : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (θ R : ℝ) (s : ℕ) : ℂ := by
  classical
  exact if s ∈ adaptiveArraySupport L Z then
    positiveDivisorArray L M lam A (adaptiveInverse M) P R h θ s else 0

def adaptiveArrayFamily (L Z : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) : Finset (ℕ → ℂ) := by
  classical
  exact (adaptiveArrayParameters L Z).image (fun a =>
    adaptiveContinuousArray L Z a.modulusResidue a.phaseResidue a.multiple lam A a.theta a.radius)

theorem adaptiveArrayFamily_card {L Z : ℕ} (hZ : 2 ≤ Z) (hLZ : L ≤ Z)
    (lam : ℝ) (A : ∀ p : ℕ, Finset (ZMod p)) :
    (adaptiveArrayFamily L Z lam A).card ≤ Z^430 := by
  classical
  exact Finset.card_image_le.trans (adaptiveArrayParameters_card hZ hLZ)

theorem adaptiveArraySupport_card (L Z : ℕ) : (adaptiveArraySupport L Z).card ≤ Z^14 := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem adaptiveArrayFamily_l1_raw {L Z : ℕ} (hL : Squarefree L) (hZ : 1 ≤ Z)
    (hLZ : L ≤ Z) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) {b : ℕ → ℂ}
    (hb : b ∈ adaptiveArrayFamily L Z lam A) :
    ∑ s ∈ adaptiveArraySupport L Z, ‖b s‖ ≤ cutoffFourierBound*(Z:ℝ)^17 := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hM,hh,hP,hPZ,ht0,ht1,hR1,hRB⟩ := mem_adaptiveArrayParameters ha (by omega)
  have hnorm (s : ℕ) (hs : s ∈ adaptiveArraySupport L Z) :
      ‖adaptiveContinuousArray L Z a.modulusResidue a.phaseResidue a.multiple lam A a.theta a.radius s‖ ≤
        cutoffFourierBound*(Z:ℝ)^3 := by
    simp only [adaptiveContinuousArray,ite_eq_left hs]
    have hs0 : 0 < s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    exact positiveDivisorArray_norm_polynomial hL hZ hLZ hs0 hP _ hlam A _ (by linarith) _ _
  have hcard : ((adaptiveArraySupport L Z).card:ℝ) ≤ (Z:ℝ)^14 := by
    exact_mod_cast adaptiveArraySupport_card L Z
  calc
    _ ≤ ∑ _s ∈ adaptiveArraySupport L Z,cutoffFourierBound*(Z:ℝ)^3 := Finset.sum_le_sum hnorm
    _ = (adaptiveArraySupport L Z).card*(cutoffFourierBound*(Z:ℝ)^3) := by simp
    _ ≤ (Z:ℝ)^14*(cutoffFourierBound*(Z:ℝ)^3) :=
      mul_le_mul_of_nonneg_right hcard (by have := cutoffFourierBound_pos; positivity)
    _ = _ := by ring

theorem adaptiveArrayFamily_l1 {L Z : ℕ} (hL : Squarefree L) (hZ : 1 ≤ Z)
    (hLZ : L ≤ Z) (hC : cutoffFourierBound ≤ (Z:ℝ)) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) {b : ℕ → ℂ}
    (hb : b ∈ adaptiveArrayFamily L Z lam A) :
    ∑ s ∈ adaptiveArraySupport L Z, ‖b s‖ ≤ (Z:ℝ)^430 := by
  calc
    _ ≤ cutoffFourierBound*(Z:ℝ)^17 := adaptiveArrayFamily_l1_raw hL hZ hLZ hlam A hb
    _ ≤ (Z:ℝ)*(Z:ℝ)^17 := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = (Z:ℝ)^18 := by ring
    _ ≤ (Z:ℝ)^430 := pow_le_pow_right₀ (by exact_mod_cast hZ) (by omega)

end Ostmann.QuadraticCenter

end

end OAI
