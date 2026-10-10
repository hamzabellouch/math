import OAI.Probability.RadialTransition.ParameterPressure

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma familyPotential_zero (t : ℝ) (S : ℕ → ℝ) :
    familyPotential t (fun _ => 0) S = corePotential t := by
  ext r
  simp [familyPotential, attractionProfile, corePotential]

lemma uniform_ideal_cutoff {βlo βhi H A : ℝ} (hlo : 0 < βlo) (hhi : βlo ≤ βhi)
    (hH : 0 ≤ H) (_hA : 0 ≤ A) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ t : ℝ, 1 ≤ t → 6912*A ≤ t →
      ∀ β ∈ Icc βlo βhi, ∀ h ∈ Icc (-H) H, ∀ a ∈ Icc (0:ℝ) A,
      ∃ κ : ℝ, 0 < κ ∧ κ ≤ β*t/3456-β*a/2 ∧ h+β*t/2+1/t+1 ≤ κ*U := by
  let K := H+βhi+2
  have hhi0 : 0 < βhi := hlo.trans_le hhi
  have hK : 0 < K := by dsimp [K]; positivity
  let U := 1+6912*K/βlo
  have hU : 1 ≤ U := by
    have hh : 0 ≤ 6912*K/βlo := by positivity
    dsimp [U]; linarith
  refine ⟨U, hU, ?_⟩
  intro t ht htA β hβ h hh a ha
  have ht0 : 0 < t := by linarith
  let κ := βlo*t/6912
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, ?_, ?_⟩
  · have hta : 6912*a ≤ t := (mul_le_mul_of_nonneg_left ha.2 (by norm_num)).trans htA
    have h1 := mul_le_mul_of_nonneg_left hta (hlo.trans_le hβ.1).le
    have h2 := mul_le_mul_of_nonneg_right hβ.1 ht0.le
    dsimp [κ]
    nlinarith
  · have hinv : 1/t ≤ 1 := (div_le_one ht0).mpr ht
    have h1 := mul_le_mul_of_nonneg_right hβ.2 ht0.le
    have h2 := mul_le_mul_of_nonneg_left ht hH
    have h3 : 2 ≤ 2*t := by linarith
    have he : κ*U = κ+t*K := by dsimp [κ, U]; field_simp
    rw [he]
    dsimp [K]
    nlinarith [hh.2, mul_nonneg hhi0.le ht0.le]

lemma family_ideal_global_active {t a : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (ha : 0 ≤ a) (htA : 6912*a ≤ t)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8) :
    ∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (familyPotential t b S) t) a β h u := by
  intro β h hβ
  obtain ⟨U, hU, hcut⟩ := uniform_ideal_cutoff hβ (le_refl β) (abs_nonneg h) ha
  obtain ⟨κ, hκ, hc, hh⟩ := hcut t ht htA β ⟨le_rfl, le_rfl⟩ h (abs_le.mp (le_refl |h|)) a ⟨ha, le_rfl⟩
  obtain ⟨u, _, hu⟩ := family_ideal_exists_active ht hβ ha hb hS hs hrow hκ hc hU hh
  exact ⟨u, hu⟩

lemma family_ideal_convex {t a : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (ha : 0 ≤ a) (htA : 6912*a ≤ t)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8) :
    ConvexOn ℝ positiveParameters (onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a)) := by
  have ht0 : 0 < t := by linarith
  apply convexOn_idealAttraction _ (family_ideal_global_active ht ha htA hb hS hs hrow)
  exact convexOn_grandPressure (continuous_familyPotential hb hS hs t) (bounded_familyPotential hb hS hs t)
    (stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrow) ht0
    (fun r hr => familyPotential_nonpos_outer hb hS ht hr)

end RadialTransition
end

end OAI
