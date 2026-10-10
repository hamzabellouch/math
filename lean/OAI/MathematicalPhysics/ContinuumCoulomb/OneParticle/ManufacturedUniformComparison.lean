import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorLower

namespace OAI

/-! For the actual manufactured field, the published one-particle inputs
give a full-domain interacting lower bound from the compressed energy. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_interacting_lower
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
      ∀ w : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric w →
      ∀ a t : ℝ, a ≤ γ/16 → 0 ≤ t →
      let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
      let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) w
      let V : Configuration (n+1) → ℝ := fun x => ∑ i,
        manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
      let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
      let e : ℝ := 2*(n+1:ℝ)*ε
      let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+e
      (E+a)*Coulomb.mass p ≤ boundedPotentialForm V p+t*Coulomb.pairEnergy p →
      (E+a-(2*(e^2+t^2*(8*(n+1:ℝ)^3*K)))/(γ/16))*Coulomb.mass w ≤
        boundedPotentialForm V w+t*Coulomb.pairEnergy w := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,_hC,hgap⟩ :=
    manufacturedSlab_uniform_tensorComplement_gap hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,max C 1,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,
    le_max_right _ _,fun m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall w hw a t ha ht => ?_⟩
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hCCH : C*S^3 ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)).trans hCH
  have hSH : S^3 ≤ H := by
    have h := mul_le_mul_of_nonneg_right (le_max_right C 1) (show 0 ≤ S^3 by positivity)
    simpa only [one_mul] using h.trans hCH
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hD₂ : 2 ≤ D := by linarith only [hR,le_max_left R R₂,hD]
  let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
  let V : Configuration (n+1) → ℝ := fun x => ∑ i,
    manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
  let e : ℝ := 2*(n+1:ℝ)*ε
  let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+e
  change (E+a)*Coulomb.mass p ≤ boundedPotentialForm V p+t*Coulomb.pairEnergy p → _
  intro hfinite
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have herr' : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ e^2 := by
    have h := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2*(n+1:ℝ)^2 by positivity)
    dsimp only [e]
    nlinarith only [h,sq_nonneg ((n+1:ℝ)*ε)]
  have hq := hgap m n D S H scale r ε η ((le_max_left _ _).trans hD) hm hS hH hCCH
    hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall w hw
  have hcomp : (E+a+γ/16)*Coulomb.mass q ≤ boundedPotentialForm V q := by
    have hmono : E+a+γ/16 ≤ E+γ/8 := by linarith only [ha]
    have h := mul_le_mul_of_nonneg_right hmono (Coulomb.mass_nonneg q)
    apply h.trans
    simpa only [q,p,finiteTensorRemainder,E,V,Nat.cast_add,Nat.cast_one] using hq
  have h := manufacturedTensor_interacting_lower hdensity hrho hHp hSp hSH hfreq hrelation
    hr hrH hrS scale hscale u hD₂ hsep hs hη hcoeff he herr' w a (γ/16) t
    (by positivity) ht hfinite hcomp
  simpa only [E,e,K,V,Nat.cast_add,Nat.cast_one] using h

end ContinuumCoulomb

end

end OAI
