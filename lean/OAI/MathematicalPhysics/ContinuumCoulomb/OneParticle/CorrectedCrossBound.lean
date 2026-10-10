import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedCrossForm
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! The off-diagonal form bound sums over spatial modes and spin components,
without a sum over exponentially many many-electron occupations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem complex_conj_sum_square_le {ι : Type*} [Fintype ι] (c z : ι → ℂ) :
    ‖∑ i, (starRingEnd ℂ) (c i)*z i‖^2 ≤ (∑ i, ‖c i‖^2)*(∑ i, ‖z i‖^2) := by
  have h : ‖∑ i, (starRingEnd ℂ) (c i)*z i‖ ≤ ∑ i, ‖c i‖*‖z i‖ := by
    simpa only [norm_mul,Complex.norm_conj] using
      norm_sum_le Finset.univ (fun i => (starRingEnd ℂ) (c i)*z i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖c i‖) (fun i => ‖z i‖))

theorem corrected_cross_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (c : SpinConfiguration 1 → Fin m → ℂ) (v : Coulomb.H1Vector 1)
    (ho : ∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0)
    (B : ℝ) (hB : ∀ x : Configuration 1,
      |manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)| ≤ B) :
    (graphBoundedCross (BoundedPotential.operator
        (fun x => manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x))
        ((manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
          oneElectronCoordinates.continuous) B hB)
      (h1Coordinates (correctedOneElectronState hfreq u c)) (h1Coordinates v))^2 ≤
      (4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j))*
        Coulomb.mass (correctedOneElectronState hfreq u c)*Coulomb.mass v := by
  let V : Configuration 1 → ℝ := fun x =>
    manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)
  let E : ℝ := (-1/2:ℝ)+freq/2
  let z (s : SpinConfiguration 1) (i : Fin m) :=
    realOrbitalPairing V E (oneElectronCorrectedMode freq u i) v s
  let err : ℝ := 4*(m:ℝ)*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j)
  have hz (s : SpinConfiguration 1) (i : Fin m) :
      ‖z s i‖^2 ≤ err*(∫ x, ‖v.value s x‖^2) :=
    correctedModePairing_square_bound hdensity hrho hH hS hfreq hrelation hR hRH hRS
      scale u hsep hs hδ hcoeff i v s
  have hsum : (∑ s, ∑ i, ‖z s i‖^2) ≤ (m:ℝ)*err*Coulomb.mass v := by
    calc
      _ ≤ ∑ s : SpinConfiguration 1, ∑ _i : Fin m, err*(∫ x, ‖v.value s x‖^2) :=
        Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun i _ => hz s i))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
          ← Finset.mul_sum,Coulomb.mass]
        ring
  have hcs := complex_conj_sum_square_le
    (fun p : SpinConfiguration 1 × Fin m => c p.1 p.2) (fun p => z p.1 p.2)
  simp only [Fintype.sum_prod_type] at hcs
  rw [← correctedOneElectronState_mass hfreq u hsep hs c] at hcs
  have hcomplex : ‖∑ s, ∑ i, (starRingEnd ℂ) (c s i)*z s i‖^2 ≤
      Coulomb.mass (correctedOneElectronState hfreq u c)*((m:ℝ)*err*Coulomb.mass v) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsum (Coulomb.mass_nonneg _))
  rw [graphBoundedCross_eq_re,corrected_complex_cross_orthogonal hfreq u c V _ B E hB v ho]
  have hre : ((∑ s, ∑ i, (starRingEnd ℂ) (c s i)*z s i).re)^2 ≤
      ‖∑ s, ∑ i, (starRingEnd ℂ) (c s i)*z s i‖^2 := by
    rw [complex_norm_sq_parts]
    nlinarith only [sq_nonneg ((∑ s, ∑ i, (starRingEnd ℂ) (c s i)*z s i).im)]
  apply hre.trans
  convert hcomplex using 1
  dsimp [err]
  ring

end ContinuumCoulomb

end

end OAI
