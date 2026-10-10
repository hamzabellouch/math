import OAI.Analysis.CircleDomains.Reflection.PrincipalReflectionTargetError

namespace OAI

/-! The conjugated smooth reflections are smooth on every fixed compact
set off the limiting pole, after a finite initial segment. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma roundReflectionPlane_contDiffAt {c z : ℂ} {r : ℝ} (hz : z≠c) :
    ContDiffAt ℝ ∞ (roundReflectionPlane c r) z := by
  have hs : ContDiffAt ℝ ∞ (fun w : ℂ => w-c) z :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have hi : ContDiffAt ℝ ∞ (fun w : ℂ => (star (w-c))⁻¹) z := by
    convert (Complex.conjCLE.contDiff.contDiffAt.comp z hs).inv
      (star_ne_zero.mpr (sub_ne_zero.mpr hz)) using 1; rfl
  have hm : ContDiffAt ℝ ∞ (fun w : ℂ => (r:ℂ)^2*(star (w-c))⁻¹) z :=
    contDiffAt_const.mul hi
  convert contDiffAt_const.add hm using 1; rfl

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedApproximation_contDiffAt (D : AnalyticReflectionData C) (i : I) (n : ℕ) {z : ℂ}
    (hz : (D.approximation.map (D.limitData.index n)).symm z≠D.center i) :
    ContDiffAt ℝ ∞ (D.reflectedApproximation i n) z := by
  have hh := (D.approximation.smooth (D.limitData.index n)).contDiffAt.comp z
    ((roundReflectionPlane_contDiffAt (r:=D.radius i) hz).comp z
      (D.approximation.inverse_smooth (D.limitData.index n)).contDiffAt)
  convert Complex.conjCLE.contDiff.contDiffAt.comp z hh using 1; rfl

lemma eventually_reflectedApproximation_contDiffOn (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∀ᶠn in atTop,ContDiffOn ℝ 1 (D.reflectedApproximation i n) T := by
  obtain ⟨K,hK,hc,ht⟩ := D.inverse_compact_away_pole i hT hpole
  filter_upwards [ht] with n hn z hz
  exact (D.reflectedApproximation_contDiffAt i n (fun h => hc (h ▸ hn hz))).of_le
    (by simp) |>.contDiffWithinAt

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
