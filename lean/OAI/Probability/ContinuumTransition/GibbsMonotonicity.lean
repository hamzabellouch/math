import OAI.Probability.ContinuumTransition.ModifiedComparison

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem gibbsFamily_antitone {U V : Space → Space → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hUV : ∀ x y, U x y ≤ V x y) (h : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily V β h ι x ≤ gibbsFamily U β h ι x := by
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (gibbsEnergy_mono x (fun i j => hUV (x i) (x j))) hβ
    linarith only [hh]
  · rfl

theorem grandIntegral_gibbs_antitone {U V : Space → Space → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hUV : ∀ x y, U x y ≤ V x y) (h : ℝ) {D : Set Space} (hD : MeasurableSet D)
    (hU : GrandFinite (gibbsFamily U β h) D) (hV : GrandFinite (gibbsFamily V β h) D) :
    grandIntegral (gibbsFamily V β h) D ≤ grandIntegral (gibbsFamily U β h) D :=
  grandIntegral_mono _ _ hD (fun n => hV.integrable (Fin n)) (fun n => hU.integrable (Fin n))
    hV.summable hU.summable (fun n x _ => gibbsFamily_antitone hβ hUV h (Fin n) x)

end ContinuumTemperature
end

end OAI
