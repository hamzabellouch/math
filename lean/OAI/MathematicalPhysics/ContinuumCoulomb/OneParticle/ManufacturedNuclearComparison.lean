import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedNuclearTensorLower
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorCoercivity

namespace OAI

/-! The actual manufactured orbital space retains full-domain complement
control after a singular nuclear perturbation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedSlab_uniform_nuclear_lower
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
      ∀ F : Position → ℝ, Measurable F → ∀ B : ℝ, 0 ≤ B →
      (∀ (z : Coulomb.H1Vector (n+1)) s i,
        Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
          B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2)) →
      ∀ w : Coulomb.H1Vector (n+1), Coulomb.Antisymmetric w →
      let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
      let p := finiteTensorProjection (localizedSpinMode freq u)
        (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
        (localizedSpinMode_partial_memLp hf u) w
      let V : Configuration (n+1) → ℝ := fun x => ∑ i,
        manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
      let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
      let e : ℝ := 2*(n+1:ℝ)*ε
      let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+e
      let g₀ : ℝ := (γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      ∀ a g t : ℝ, 0 < g → 0 ≤ t → B*(n+1)+|a|+g ≤ g₀ →
      (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
      (E+a-3*(e^2+t^2*(8*(n+1:ℝ)^3*K)+B^2*((n+1:ℝ)+2*K)*(n+1))/g)*Coulomb.mass w ≤
        nuclearPerturbedForm V F w+t*Coulomb.pairEnergy w := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,_hC,hgap⟩ :=
    manufacturedSlab_uniform_tensorComplement_coercivity hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,max C 1,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,
    le_max_right _ _,?_⟩
  intro m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall
    F hF B hB herror w hw
  dsimp only
  intro a g t hg ht hsmallB hfinite
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hCCH : C*S^3 ≤ H := (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)).trans hCH
  have hSH : S^3 ≤ H := by
    have h := mul_le_mul_of_nonneg_right (le_max_right C 1) (show 0 ≤ S^3 by positivity)
    simpa only [one_mul] using h.trans hCH
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hD₂ : 2 ≤ D := by linarith only [hR,le_max_left R R₂,hD]
  let p := finiteTensorProjection (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let q := finiteTensorRemainder (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let V : Configuration (n+1) → ℝ := fun x => ∑ i,
    manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
  let e : ℝ := 2*(n+1:ℝ)*ε
  have he : 0 ≤ e := by dsimp [e]; positivity
  have herr' : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ e^2 := by
    have h := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2*(n+1:ℝ)^2 by positivity)
    dsimp [e]
    nlinarith only [h,sq_nonneg ((n+1:ℝ)*ε)]
  have hcoercive := hgap m n D S H scale r ε η ((le_max_left _ _).trans hD) hm hS hH hCCH
    hscale hr hrH hrS hε hη hηδ u hsep hcoeff herr hsmall w hw
  have hsmallB' : B*(n+1:ℕ)+|a|+g ≤
      (γ/8)/(2*((n+1:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hsmallB
  have hcomp := nuclearPerturbed_coercive_complement (show 1 ≤ n+1 by omega)
    V F hB q E a _ g (fun s i => (herror q s i).2) (by simpa only [E,V,q,Nat.cast_add,Nat.cast_one] using hcoercive) hsmallB'
  have h := manufacturedTensor_nuclear_interacting_lower hdensity hrho hHp hSp hSH hfreq hrelation
    hr hrH hrS scale hscale u hD₂ hsep hs hη hcoeff he herr' F hF B hB herror w a g t hg ht hfinite hcomp
  simpa only [e,Nat.cast_add,Nat.cast_one] using h

end ContinuumCoulomb

end

end OAI
