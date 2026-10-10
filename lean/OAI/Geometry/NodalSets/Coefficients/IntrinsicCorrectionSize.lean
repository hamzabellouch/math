import Mathlib.Analysis.Complex.OperatorNorm
import OAI.Geometry.NodalSets.Coefficients.IntrinsicRealCorrection
import OAI.Geometry.NodalSets.Coefficients.RoundCorrectionSize

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem intrinsic_real_correction_size (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ C > 0, ∀ (u H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u →
      (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n) u
      ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      (∀ x, DerivativeBound (r+1) R x (eps*H x)) →
      (∀ x ∈ Q, ∀ i, i ≤ r+2 → ‖iteratedFDeriv ℝ i u x‖ ≤ B*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
      let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
      let alpha := fun x ↦ f x*u x
      let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
      tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
      (∀ x i, i ≤ r → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
        C*eps*(n:ℝ)^(137*r+267)) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x := by
  obtain ⟨M,hM,hm⟩ := intrinsicCorrectionResidual_bound A rho hrs hQ (r+1)
  obtain ⟨C,hC,hsize⟩ := round_correction_size hQ r hB
  refine ⟨C*M,by positivity,?_⟩
  intro u H hu hH n hn eps heps R hR hsup hRb hub hjet
  obtain ⟨hsm,hs,hbound⟩ := hm (seedEigenvalue n) u hR hsup
  let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
  have hR0 : ContDiff ℝ ∞ R0 := Complex.reCLM.contDiff.comp hsm
  have hs0 : tsupport R0 ⊆ Q := (intrinsicRealCorrectionResidual_support A rho _ u).trans hs
  have hR0b (x : Yau.Jets.Coord) (i : ℕ) (hi : i ≤ r+1) :
      ‖iteratedFDeriv ℝ i R0 x‖ ≤ (M*eps)*H x := by
    have h := Complex.reCLM.norm_iteratedFDeriv_comp_left hsm.contDiffAt
      (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top)) (x := x)
    rw [Complex.reCLM_norm,one_mul] at h
    have hb := hbound (fun y ↦ eps*H y) (fun y ↦ mul_nonneg heps.le (hH y).le) hRb x i hi
    exact h.trans (by simpa [mul_assoc] using hb)
  obtain ⟨hf,ha,hbeta,has,hbs,hb⟩ := hsize u R0 H hu hR0 hs0 hH n hn (M*eps)
    (by positivity) hub (fun x _ i hi ↦ hR0b x i hi) hjet
  refine ⟨hf,ha,hbeta,has.trans hs0,hbs.trans hs0,?_,?_⟩
  · intro x i hi
    simpa [mul_assoc] using hb x i hi
  · obtain ⟨f,hf',hfc,hfs,hval,heq⟩ := round_supported_exact_correction u R0 H hQ
      (Subset.refl Q) hu hR0 hs0 hn (fun x _ ↦ hH x) hjet
    have he : f = fun x ↦ R0 x / roundCorrectionDenominator u n x := funext hval
    subst f
    intro x
    convert heq x using 1
    congr 1
    congr 1
    funext y i
    ring

end
end Yau.Target

end OAI
