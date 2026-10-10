import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeODEUniqueness

namespace OAI

/-! Subtracting an outgoing parameter derivative removes the physical chain source. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFreeChainSource (U : E₄) : E₄ :=
  ((0,-Complex.I*U.1.1),(0,Complex.I*U.2.1))

theorem spectralFreeChain_difference (b ζ η a c : ℂ)
    (U₀ U₁ P N DP DN : ℝ → E₄) (r : ℝ)
    (hU₀ : U₀ r = a • P r + c • N r)
    (hU₁ : HasDerivAt U₁ (spectralFreePhysicalPairField b ζ η r (U₁ r) +
      spectralFreeChainSource (U₀ r)) r)
    (hDP : HasDerivAt DP (spectralFreePhysicalPairField b ζ η r (DP r) +
      spectralFreeChainSource (P r)) r)
    (hDN : HasDerivAt DN (spectralFreePhysicalPairField b ζ η r (DN r) +
      spectralFreeChainSource (N r)) r) :
    HasDerivAt (fun s => U₁ s - (a • DP s + c • DN s))
      (spectralFreePhysicalPairField b ζ η r (U₁ r - (a • DP r + c • DN r))) r := by
  apply (hU₁.sub ((hDP.const_smul a).add (hDN.const_smul c))).congr_deriv
  rw [hU₀]
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralFreeChainSource,
      Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring

end DefocusingNLS

end OAI
