import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialResidue
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialPowers
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortModelLow

namespace OAI

/-! Summing the actual radial lattice-to-residue error over an arbitrary
level selector. All constants precede the selector and its coefficient family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.radial_selected_error
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδsmall : δ ≤ 1/6) :
    ∃ B K E : ℝ, 1 ≤ B ∧ 0 ≤ K ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
      (X R U C : ℝ), 0 < R → 0 < U → 0 < C → C ≤ Real.sqrt (B*U) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      ‖∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)‖ ≤
      (K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*
        (∑ r ∈ S, ‖α r‖) := by
  obtain ⟨B,K,E,hB,hK,hE,hbound⟩ := hW.radial_short_model_error hδ hs
  refine ⟨B,K,E,hB,hK,hE,?_⟩
  intro w S α X R U C hR hU hC hCD hS hY
  have hbnd (r : Eisenstein) (hr : r ∈ S) :
      ‖angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C‖ ≤
      K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
    obtain ⟨hp,hsr,hn⟩ := hS r hr
    have hX : 0 < X := zero_lt_one.trans_le ((hW.length_one (w r)).trans (hY r hr))
    have hnr : 0 ≤ norm r := norm_nonneg r
    have hy := Real.rpow_le_rpow (zero_lt_one.trans_le (hW.length_one (w r))).le
      (hY r hr) hs.le
    have hn1 := Real.rpow_le_rpow_of_nonpos hR hn (show δ-1/6 ≤ 0 by linarith)
    have hn2 := Real.rpow_le_rpow_of_nonpos hR hn (by norm_num : (-1/6:ℝ) ≤ 0)
    apply (hbound (w r) r hp hsr U C hU hC hCD).trans
    gcongr
  calc
    _ ≤ ∑ r ∈ S, ‖α r‖*‖angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C‖ := by
      simpa only [norm_mul] using norm_sum_le S (fun r => α r*
        (angularSmoothModel r 0 (W (w r)) U-
          metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C))
    _ ≤ ∑ r ∈ S, ‖α r‖*(K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+
        E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hbnd r hr) (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
