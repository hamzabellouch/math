import OAI.Analysis.LipschitzHilbert.Estimates.FiniteBinCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinEnergy

namespace OAI

/-! Summing the actual projected bin commutators. The bin energy estimate
leaves only one factor of the number of bins in the squared error. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem totalBinError_energy (k : SchwartzMap ℝ ℂ) (N J : ℕ)
    (I : Finset ℕ) (hI : I⊆Finset.range (2*J+1))
    (topLength W : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    let E := fun n : I => finiteBinError k verticalBinProfile N topLength W
      (verticalBinCenter J W n) u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)
    MemLp (fun z => ∑ n : I, E n z) 2 planeMeasure ∧
      (∫ z, ‖∑ n : I, E n z‖^2 ∂planeMeasure)≤
        (I.card:ℝ)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
          (topLength*W*R)^2)*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  intro E
  let A := 4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
    (topLength*W*R)^2
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _)
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  have hb (n : I) : ∀ omega, planarFourier (P n) omega≠0 → |omega.2|≤R := by
    intro omega hn
    apply hband omega
    intro hz
    apply hn
    dsimp only [P]
    rw [schwartzVerticalProjection_fourier,hz,mul_zero]
  have he (n : I) : MemLp (E n) 2 planeMeasure ∧
      (∫ z, ‖E n z‖^2 ∂planeMeasure)≤A*(∫ z, ‖P n z‖^2 ∂planeMeasure) :=
    finiteBinCommutator_energy k verticalBinProfile N topLength W
      (verticalBinCenter J W n) htop hW u hu (P n) R hR (hb n)
  refine ⟨?_,?_⟩
  · simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun n _ => (he n).1)
  · have hs := weighted_integral_sum_square planeMeasure E (fun n => (he n).1)
      (fun _ => (1:ℝ)) (fun _ => by norm_num)
    simp only [div_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      Fintype.card_coe] at hs
    have hE : (∑ n : I, ∫ z, ‖E n z‖^2 ∂planeMeasure)≤A*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      calc
        _ ≤ ∑ n : I, A*(∫ z, ‖P n z‖^2 ∂planeMeasure) :=
          Finset.sum_le_sum fun n _ => (he n).2
        _ = A*(∑ n : I, ∫ z, ‖P n z‖^2 ∂planeMeasure) := (Finset.mul_sum ..).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hA
          simpa only [P,Finset.sum_coe_sort I (fun n : ℕ =>
            ∫ z, ‖schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f z‖^2
              ∂planeMeasure)] using verticalBin_schwartz_energy_le f J W hW I hI
    exact hs.trans (by simpa only [mul_assoc,A] using
      mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg I.card))

end LipschitzHilbert.PacketRepresentation

end

end OAI
