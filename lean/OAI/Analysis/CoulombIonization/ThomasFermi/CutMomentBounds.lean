import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialCountSelection

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

lemma orderedCutForm_mass_sum {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∑ c : Fin N → Fin 2, formMass (orderedCutForm p hp ψ c)) = formMass ψ := by
  simp_rw [orderedCutForm_mass]
  exact spatial_cut_mass p hp hψ

lemma cutOutMoment_le_second {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^r*formMass (orderedCutForm p hp ψ c)) ≤
      (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass (orderedCutForm p hp ψ c))^(r/2) := by
  have hh := (Real.concaveOn_rpow (p := r/2) (by positivity) (by linarith)).le_map_sum
    (t := Finset.univ) (w := fun c : Fin N → Fin 2 => formMass (orderedCutForm p hp ψ c))
    (p := fun c => (cutOutNumber c:ℝ)^2)
    (fun c _ => formMass_nonneg _) ((orderedCutForm_mass_sum p hp hψ).trans hm)
    (fun c _ => sq_nonneg (cutOutNumber c:ℝ))
  have he (c : Fin N → Fin 2) : ((cutOutNumber c:ℝ)^2)^(r/2) = (cutOutNumber c:ℝ)^r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simpa only [smul_eq_mul,he,mul_comm] using hh

lemma cutOutMoment_le_bound {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) {B : ℝ}
    (hB : (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass (orderedCutForm p hp ψ c)) ≤ B) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^r*formMass (orderedCutForm p hp ψ c)) ≤ B^(r/2) :=
  (cutOutMoment_le_second p hp hψ hm hr hr2).trans
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun c _ => mul_nonneg (sq_nonneg _) (formMass_nonneg _)))
      hB (by positivity))

lemma radialCut_out_lower_moments {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let B := ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) ≤ B^(1/2:ℝ) ∧
    (∑ c : Fin N → Fin 2, ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*
      formMass (orderedCutForm p hp ψ c)) ≤ B^(2/3:ℝ)+B^(1/2:ℝ) := by
  dsimp only
  have hB := radialCut_out_second_moment hψ y ht hb hR
  have h1 := cutOutMoment_le_bound _ _ hψ hm (r := 1) (by norm_num) (by norm_num) hB
  have h4 := cutOutMoment_le_bound _ _ hψ hm (r := 4/3) (by norm_num) (by norm_num) hB
  simp only [Real.rpow_one] at h1
  norm_num only [show (4/3:ℝ)/2 = 2/3 by norm_num] at h4
  refine ⟨h1,?_⟩
  simp only [add_mul,Finset.sum_add_distrib]
  exact add_le_add h4 h1

end CoulombAtom

end

end OAI
