import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierWitness
import OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs
import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientBounds
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorDyadicBridge
local notation "O" => HeckeFamily.O

theorem dyadic_frequency_bound (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : Character) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end SevenEighths.HeckeDetectorFrequency

end

end OAI
