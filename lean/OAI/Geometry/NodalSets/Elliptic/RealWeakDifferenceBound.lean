import OAI.Geometry.NodalSets.Elliptic.RealL2SmoothTesting
import OAI.Geometry.NodalSets.Elliptic.RealWeakTranslationPairing

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_weak_difference_test_bound {n : ℕ} (u g : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hgm : MemLp g 2 volume) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x))
    (h : ℝ) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) :
    |∫ x, realDifferenceQuotient i h u x*psi x| ≤
      ‖hgm.toLp g‖*Real.sqrt (∫ x, (psi x)^2) := by
  have hpsi := real_compact_continuous_memLp psi hp.continuous hc
  let R : ℝ → ℝ := fun t : ℝ ↦ ∫ x : Coord n, u x*psi (x+Pi.single i t)
  let C : ℝ := ‖hgm.toLp g‖*‖hpsi.toLp psi‖
  have hpt (t : ℝ) : ContDiff ℝ ∞ (fun x : Coord n ↦ psi (x+Pi.single i t)) :=
    hp.comp (contDiff_id.add contDiff_const)
  have hpct (t : ℝ) : HasCompactSupport (fun x : Coord n ↦ psi (x+Pi.single i t)) :=
    hc.comp_homeomorph (Homeomorph.addRight (Pi.single i t : Coord n))
  have hpmt (t : ℝ) : MemLp (fun x : Coord n ↦ psi (x+Pi.single i t)) 2 volume := real_compact_continuous_memLp _ (hpt t).continuous (hpct t)
  have hd (t : ℝ) : HasDerivAt R (-(∫ x, g x*psi (x+Pi.single i t))) t := by
    have ht := real_translate_pairing_hasDerivAt u psi hu hum hp hc i t
    rw [hweak _ (hpt t) (hpct t)] at ht
    exact ht
  have hbound (t : ℝ) : ‖deriv R t‖ ≤ C := by
    have ht : (realL2Translate (Pi.single i t) (hpsi.toLp psi) : Coord n → ℝ) =ᵐ[volume]
        (fun x ↦ psi (x+Pi.single i t)) :=
      (realL2Translate_ae (Pi.single i t) (hpsi.toLp psi)).trans
        ((measurePreserving_add_right (G := Coord n) volume (Pi.single i t)).quasiMeasurePreserving.ae_eq_comp
          hpsi.coeFn_toLp)
    have hi := real_L2_inner_reps (hgm.toLp g) (realL2Translate (Pi.single i t) (hpsi.toLp psi))
      g (fun x ↦ psi (x+Pi.single i t)) hgm.coeFn_toLp ht
    rw [(hd t).deriv,norm_neg,← hi.2]
    have hn := norm_inner_le_norm (𝕜 := ℝ) (hgm.toLp g) (realL2Translate (Pi.single i t) (hpsi.toLp psi))
    simpa only [realL2Translate_norm,C] using hn
  have hosc := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) ↦ (hd t).differentiableAt) (fun t _ ↦ hbound t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ (0:ℝ)) (Set.mem_univ (-h))
  have hid : (∫ x, u x*realDifferenceQuotient i (-h) psi x) = (-h)⁻¹*(R (-h)-R 0) := by
    have he : (fun x ↦ u x*realDifferenceQuotient i (-h) psi x) =
        fun x ↦ (-h)⁻¹*(u x*psi (x+Pi.single i (-h))-u x*psi x) := by
      funext x; unfold realDifferenceQuotient; ring
    have hi1 : Integrable (fun x ↦ u x*psi (x+Pi.single i (-h))) := hum.integrable_mul (hpmt (-h))
    have hi0 : Integrable (fun x ↦ u x*psi x) := hum.integrable_mul hpsi
    rw [he,integral_const_mul,integral_sub hi1 hi0]
    simp only [R,Pi.single_zero,add_zero]
  have hpair := (real_differenceQuotient_pairing i h u psi hum hpsi).2.2
  have hsqrt : Real.sqrt (∫ x, (psi x)^2)=‖hpsi.toLp psi‖ := by
    rw [← real_toLp_norm_sq psi hpsi,Real.sqrt_sq (norm_nonneg _)]
  rw [hpair,abs_neg,hid,abs_mul,hsqrt]
  change |(-h)⁻¹| *|R (-h)-R 0| ≤ C
  by_cases hh : h=0
  · subst h
    simp only [neg_zero,inv_zero,abs_zero,zero_mul]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have ho : |R (-h)-R 0| ≤ C*|h| := by
      simpa only [sub_zero,Real.norm_eq_abs,abs_neg] using hosc
    calc
      _ ≤ |(-h)⁻¹| *(C*|h|) := mul_le_mul_of_nonneg_left ho (abs_nonneg _)
      _ = C := by rw [abs_inv,abs_neg]; field_simp [abs_ne_zero.mpr hh]

theorem real_weak_derivative_difference_bound {n : ℕ} (u g : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hgm : MemLp g 2 volume) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x)) (h : ℝ) :
    MemLp (realDifferenceQuotient i h u) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h u x)^2) ≤ ∫ x, (g x)^2 := by
  have hm := realDifferenceQuotient_memLp i h u hum
  have hn := real_L2_norm_le_of_smooth_test_bound _ hm ‖hgm.toLp g‖ (norm_nonneg _)
    (fun psi hp hc ↦ real_weak_difference_test_bound u g hu hum hgm i hweak h psi hp hc)
  have hsq : ‖hm.toLp (realDifferenceQuotient i h u)‖^2 ≤ ‖hgm.toLp g‖^2 := by
    nlinarith [norm_nonneg (hm.toLp (realDifferenceQuotient i h u)),norm_nonneg (hgm.toLp g)]
  rw [real_toLp_norm_sq,real_toLp_norm_sq] at hsq
  exact ⟨hm,hsq⟩

end
end Yau

end OAI
