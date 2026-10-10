import OAI.NumberTheory.CubicMoment.Angular.AngularRealScaleLargeMoment
import OAI.NumberTheory.CubicMoment.Estimates.CoreBlockGeometry

namespace OAI

/-! The proved large-conductor estimate on the concrete frequency cover;
the cube-factor count cancels its conductor weight. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_block_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ)
      (v e : Eisenstein) (u : ℝ) (H : Finset Eisenstein), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
      (L r)^κ ≤ coreDyadicConductor i j →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) → H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    angular_large_conductor_real_scales ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
  let K : ℝ := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    exact ⟨1,mem_nonzeroNormBall.mpr ⟨by norm_num [norm_one_eq],one_ne_zero⟩⟩
  refine ⟨η,σ,18*C*K,ν,hη,hη₁,hσ,by positivity,hν,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hbound⟩ := hbound L W hL hW hlo hhi
  obtain ⟨T₂,h729⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hσ).eventually_ge_atTop (729:ℝ))
  refine ⟨max T₁ T₂,?_⟩
  intro r X B i j v e u H hT₀ hprod hX hB hBL hDB hlarge hv he hvN heN hu hH
  have h729' : 729 ≤ (L r)^σ := h729 _ ((le_max_right _ _).trans hT₀)
  have hRam : ∀ a ∈ nonzeroNormBall 729, a ≠ 0 ∧ norm a ≤ (L r)^σ := by
    intro a ha
    have hm := mem_nonzeroNormBall.mp ha
    exact ⟨hm.2,hm.1.trans h729'⟩
  have hJ : ∀ a ∈ coreDyadicCubeFactors B i j, a ≠ 0 ∧
      norm a^3*((2:ℝ)^i*((2:ℝ)^j)^2) ≤ (L r)^(1+η) := by
    intro a ha
    have hm := coreDyadicCubeFactors_spec hB ha
    exact ⟨hm.1,hm.2.trans hBL⟩
  have hh := hbound r X ((2:ℝ)^i) ((2:ℝ)^j) v e u
    (nonzeroNormBall 729) (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
    (coreDyadicCubeFactors B i j) H ((le_max_left _ _).trans hT₀)
    hprod hX (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    (hDB.trans hBL) hlarge hv he hvN heN hu hRam hJ
    (fun _ ha => squarefreePrimaryDyad_gramDyad ha)
    (fun _ ha => squarefreePrimaryDyad_gramDyad ha) hH
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (coreDyadicCubeFactors_card_weight hB i j)
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hK.le) (sq_nonneg (L r)))
      (Real.rpow_nonneg (zero_le_one.trans (hL r)) (-ν)))
  convert hm using 1 <;> dsimp [K,coreDyadicConductor] <;> ring

end CubicFirstMoment

end

end OAI
