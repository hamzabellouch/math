import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

 theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0<B ∧ ∀(ν : Character)(P σ v t : ℝ),0<P → lo≤σ → σ≤hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I‖≤B ∧
      (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
