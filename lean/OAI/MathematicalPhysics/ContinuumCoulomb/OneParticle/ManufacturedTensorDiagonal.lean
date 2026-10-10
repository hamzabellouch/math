import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorProjection

namespace OAI

/-! Actual compressed manufactured-field energy and kinetic estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedTensorState_diagonal_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (c : (Fin (n+1) → Fin ((2*m+1)+1)) → ℂ) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
    (boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) p-(n+1:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)^2 ≤
      (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j)*
        Coulomb.mass p*Coulomb.mass p := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hsum (x : Configuration (n+1)) :
      |∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)| ≤
        (n+1:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => hB (Coulomb.position x i))
  have hc := finiteTensorState_diagonal_square_bound hdensity
    (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_C2 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hfreq scale u hη hcoeff)
    (fun a b => by
      have h := localizedSpinMode_inner hfreq u hsep hs a b
      by_cases hab : a=b <;> simpa only [hab,ite_true,ite_false] using h)
    (manufacturedSlabPotential rho H S freq scale u)
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u)
    ((-1/2:ℝ)+freq/2) ((n+1:ℝ)*B) hsum
    (fun a s x => by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
        Complex.ofReal_one,Complex.ofReal_ofNat] using
        localizedSpinResidual_operator hrelation H S scale u a s x) c
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (localizedSpinResidual_sum_bound hrho hH hS hfreq hR hRH hRS scale u hsep hs hη hcoeff)
    (sq_nonneg _)

theorem localizedTensorState_kinetic_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H)
    (hfreq : 0 < freq) (hrelation : freq^2 = 4*Real.pi*rho)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) (hscale : 0 ≤ scale) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hD : 2 ≤ D) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (hε : 0 ≤ ε)
    (herr : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D R u j) ≤ ε^2)
    (c : (Fin (n+1) → Fin ((2*m+1)+1)) → ℂ) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
    Coulomb.kinetic p ≤
      ((n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+ε)*Coulomb.mass p := by
  let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c
  have hb := localizedTensorState_diagonal_square_bound hdensity hrho hH hS hfreq hrelation
    hR hRH hRS scale u hsep hs hη hcoeff c
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right herr (Coulomb.mass_nonneg p)) (Coulomb.mass_nonneg p))
  have hnonneg : 0 ≤ ε*Coulomb.mass p := mul_nonneg hε (Coulomb.mass_nonneg p)
  have hupper : boundedPotentialForm (fun x => ∑ i,
      manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)) p ≤
      ((n+1:ℝ)*((-1/2:ℝ)+freq/2)+ε)*Coulomb.mass p := by
    change (_-(n+1:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)^2 ≤ _ at hb'
    nlinarith only [hb',hnonneg]
  have hk := manufacturedSlab_manyElectron_kinetic_lower hrho hH hS hSH hscale hrelation u
    (fun i j hij => hD.trans (hsep i j hij)) hη hcoeff p
  change Coulomb.kinetic p ≤
    ((n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+ε)*Coulomb.mass p
  simp only [Nat.cast_add,Nat.cast_one] at hk ⊢
  nlinarith only [hk,hupper]

end ContinuumCoulomb

end

end OAI
