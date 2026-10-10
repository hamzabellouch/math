import OAI.Probability.ContinuumTransition.ModifiedEnergy

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_radial (φ : ℝ → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => φ ‖x-y‖) x = realPairEnergy φ x := by
  unfold gibbsEnergy realPairEnergy
  ring

theorem gibbsFamily_radial (φ : ℝ → ℝ) (β h : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily (fun x y => φ ‖x-y‖) β h ι x =
      Real.exp (h*Fintype.card ι)*symmetricWeight φ β x := by
  unfold gibbsFamily symmetricWeight
  split_ifs
  · rw [gibbsEnergy_radial, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem familyTerm_radial (φ : ℝ → ℝ) (β h L : ℝ) (n : ℕ) :
    familyTerm (gibbsFamily (fun x y => φ ‖x-y‖) β h) (cube L) n =
      Real.exp (h*n)*partition φ β L n := by
  unfold familyTerm familyIntegral
  simp_rw [gibbsFamily_radial, Fintype.card_fin]
  rw [integral_const_mul, mul_div_assoc]
  simpa only [generalPartition, Fintype.card_fin] using
    congrArg (fun a : ℝ => Real.exp (h*n)*a) (generalPartition_eq_partition φ β L n)

theorem grandIntegral_radial (φ : ℝ → ℝ) (t β h L : ℝ) :
    grandIntegral (gibbsFamily (fun x y => φ ‖x-y‖) β (t*h)) (cube L) =
      grandPartition φ t β h L := by
  unfold grandIntegral grandPartition
  simp_rw [familyTerm_radial]

theorem CellLowerBound.mono {t : ℝ} {σ R : ℕ → ℝ} {U V : Space → Space → ℝ}
    (hU : CellLowerBound t σ R U) (hUV : ∀ x y, U x y ≤ V x y) : CellLowerBound t σ R V :=
  fun x y => (hU x y).trans (hUV x y)

theorem physical_cellLowerBound {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) :
    CellLowerBound t σ R (fun x y => physicalProfile t σ R ‖x-y‖) := by
  intro x y
  have hb := attraction_le_mixedEnvelope ht hσ hR hs x y
  change attraction t σ R ‖x-y‖ ≤ physicalCoupling t σ R (cellIndex x) (cellIndex y) at hb
  dsimp only [physicalProfile]
  split_ifs
  · linarith only [hb]
  · linarith only [hb, coreProfile_nonneg t ‖x-y‖]

theorem masked_physical_cellLowerBound {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (p q : Space → Space → ℝ) (hp : ∀ x y, 0 ≤ p x y)
    (hpc : ∀ x y, cellIndex x = cellIndex y → p x y = 1) (hq : ∀ x y, q x y ≤ 1) :
    CellLowerBound t σ R (fun x y => p x y*coreProfile t ‖x-y‖-q x y*attraction t σ R ‖x-y‖) := by
  intro x y
  have hb := attraction_le_mixedEnvelope ht hσ hR hs x y
  have ha := attraction_nonneg ht hσ hR ‖x-y‖
  have hc := coreProfile_nonneg t ‖x-y‖
  have hq' := mul_le_mul_of_nonneg_right (hq x y) ha
  change attraction t σ R ‖x-y‖ ≤ physicalCoupling t σ R (cellIndex x) (cellIndex y) at hb
  dsimp only
  split_ifs with hxy
  · rw [hpc x y hxy]
    nlinarith only [hb, hq']
  · nlinarith only [hb, hq', mul_nonneg (hp x y) hc]

end ContinuumTemperature
end

end OAI
