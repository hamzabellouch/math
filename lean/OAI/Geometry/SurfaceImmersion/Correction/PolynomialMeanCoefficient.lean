import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticPhases
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationBounds

namespace OAI

/-! The polynomial contribution to the quadratic zero-phase coefficient. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma pairPhases_smooth {φ ψ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    ∀ j, ContDiff ℝ ∞ (pairPhases φ ψ j) := by
  intro j
  fin_cases j
  · exact hφ
  · exact hψ
  · exact contDiff_const

lemma pairDirections_smooth {H K : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ∀ j, ContDiff ℝ ∞ (pairDirections H K j) := by
  intro j
  fin_cases j
  · exact hH
  · exact hK
  · exact contDiff_const

lemma weighted_starField {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {H : Base → Fin 4 → ℂ} (hs : 0 < s) (hC : 0 ≤ C) (hH : ContDiff ℝ ∞ H)
    (hb : WeightedBound U s m C H) : WeightedBound U s m C (starField H) := by
  apply WeightedBound.pi hU hs hC
  · intro a
    exact (Complex.conjCLE.contDiff.comp (contDiff_pi.mp hH a)).contDiffOn
  · intro a
    have hh := (hb.component hU hs.le hC hH.contDiffOn a).linear hU hs.le
      (contDiff_pi.mp hH a).contDiffOn Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp

namespace Perturbation

def quadraticMeanCoefficient {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField H)) τ 1 (p, t)).re / 4

lemma quadraticMeanCoefficient_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticMeanCoefficient P ε G φ H τ t) U := by
  have hs := fun l => conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
    (pairDirections_smooth hH (starField_smooth hH)) hO hQ τ 1 t
  exact (Complex.reCLM.contDiff.comp_contDiffOn
    (ContDiffOn.sum fun l _ => (hs l).const_smul (ε ^ (l.val + 1)))).div_const 4

/-- This is the actual zero-phase Hessian term, with the fixed polynomial
loss, and with the square of the oscillatory amplitude retained. -/
theorem quadraticMeanCoefficient_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (H : Base → Fin 4 → ℂ) (s τ ε C : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ H →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * ε * C ^ 2 / τ ^ loss P) (quadraticMeanCoefficient P ε G φ H τ t) := by
  obtain ⟨D, hD, hd⟩ := compact_conjugated_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨D / 4, div_nonneg hD (by norm_num), ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ hGb hHb hφb t ht
  have hpb : ∀ j v, WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (pairPhases φ (fun p => -φ p) j) p (coordinateVector v)) := by
    intro j v
    fin_cases j
    · exact hφb v
    · have hh := (hφb v).neg hU.uniqueDiffOn
        ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).contDiffOn
      change WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (fun q => -φ q) p (coordinateVector v))
      simpa only [fderiv_fun_neg, neg_apply] using hh
    · change WeightedBound U s (m + order P) F (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
      simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
        (weightedBound_zero U s (m + order P)).mono_const hF
  have hhb : ∀ j, WeightedBound U s (m + order P) (![C, C, 1] j) (pairDirections H (starField H) j) := by
    intro j
    fin_cases j
    · exact hHb
    · exact weighted_starField hU.uniqueDiffOn hs hC.le hH hHb
    · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
  have hh := hd G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField H)) s τ ε ![C, C, 1]
    hτ hs hτs hs1 hε hε1 (fun j => by fin_cases j; exact hC; exact hC; norm_num)
    hG (pairPhases_smooth hφ hφ.neg) (pairDirections_smooth hH (starField_smooth hH))
    hGQ hGb hhb hpb t ht 1
  have hsm : ContDiffOn ℝ ∞ (fun p => conjugated P ε G
      (pairPhases φ (fun p => -φ p)) (pairDirections H (starField H)) τ 1 (p, t)) U :=
    ContDiffOn.sum fun l _ =>
      (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
        (pairDirections_smooth hH (starField_smooth hH)) hO (fun _ hp => hQO (hGQ hp)) τ 1 t).const_smul _
  have hr := hh.linear hU.uniqueDiffOn hs.le hsm Complex.reCLM
  have hn : 0 ≤ D * ε * (C * C * 1) / τ ^ loss P := by positivity
  have hr' := hr.mono_const (mul_le_of_le_one_left hn (by simp : ‖Complex.reCLM‖ ≤ 1))
  have hf := hr'.const_smul hU.uniqueDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hsm) (1 / 4 : ℝ)
  convert hf using 1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
      show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  · funext p
    simp only [quadraticMeanCoefficient, Function.comp_def, Complex.reCLM_apply, smul_eq_mul]
    ring

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
