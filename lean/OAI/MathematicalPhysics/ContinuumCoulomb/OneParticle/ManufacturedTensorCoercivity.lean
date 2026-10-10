import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedCoercivity

namespace OAI

/-! Uniform kinetic coercivity on the actual spinful tensor complement. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_tensorComplement_coercivity
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
      ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 ≤ scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ v : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric v →
      let hf := lt_of_lt_of_le zero_lt_one hfreq
      let q := finiteTensorRemainder (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) v
      ((γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1)))*
        (Coulomb.mass q+2*Coulomb.kinetic q) ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) q-(n+1:ℕ)*((-1/2:ℝ)+freq/2)*Coulomb.mass q := by
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hgap⟩ :=
    manufacturedSlab_uniform_tensorComplement_gap hp hv hdensity hfreq hrho hrelation
  refine ⟨γ,R,S₀,δ,max C 1,hγ,hγsmall,hR,hS₀,hδ,le_max_right _ _,
    fun m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall v ha => ?_⟩
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSbase : S^3 ≤ max C 1*S^3 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right C 1)
      (pow_nonneg hSpos.le 3)
  have hSH : S^3 ≤ H := hSbase.trans hCH
  have hCH' : C*S^3 ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hSpos.le 3)).trans hCH
  have hsep₂ (i j : Fin (m+1)) (hij : i≠j) : 2 ≤ ‖u i-u j‖ :=
    (by linarith : 2 ≤ D).trans (hsep i j hij)
  have hg := hgap m n D S H scale r ε η hD hm hS hH hCH' hscale hr hrH hrS
    hε hη hηδ u hsep hcoeff herr hsmall v ha
  exact manufacturedSlab_coercive_of_gap hrho hHpos hSpos hSH hscale hrelation
    u hsep₂ hη hcoeff _ (by linarith) (by positivity) hg

end ContinuumCoulomb

end

end OAI
