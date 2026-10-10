import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronProjectedLower

namespace OAI

/-! The same residual controls the actual compressed diagonal form, with no
entrywise sum over occupation configurations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem corrected_residual_sum_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (c : SpinConfiguration 1 → Fin m → ℂ) (v : Coulomb.H1Vector 1) :
    ‖∑ s, ∑ i, (starRingEnd ℂ) (c s i)*
      realOrbitalPairing (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) ((-1/2:ℝ)+freq/2) (oneElectronCorrectedMode freq u i) v s‖^2 ≤
      (4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j))*
        Coulomb.mass (correctedOneElectronState hfreq u c)*Coulomb.mass v := by
  let z (s : SpinConfiguration 1) (i : Fin m) :=
    realOrbitalPairing (fun x => manufacturedSlabPotential rho H S freq scale u
      (oneElectronCoordinates x)) ((-1/2:ℝ)+freq/2) (oneElectronCorrectedMode freq u i) v s
  let err := 4*(m:ℝ)*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j)
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
  have h := hcs.trans (mul_le_mul_of_nonneg_left hsum (Coulomb.mass_nonneg _))
  convert h using 1
  dsimp [err]
  ring

theorem corrected_diagonal_residual_identity {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (c : SpinConfiguration 1 → Fin m → ℂ)
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B) :
    boundedPotentialForm V (correctedOneElectronState hfreq u c)-
      E*Coulomb.mass (correctedOneElectronState hfreq u c) =
      (∑ s, ∑ i, (starRingEnd ℂ) (c s i)*
        realOrbitalPairing V E (oneElectronCorrectedMode freq u i)
          (correctedOneElectronState hfreq u c) s).re := by
  have ho := correctedOneElectronOrbital_orthonormal hfreq u hsep hs
  have hi (s : SpinConfiguration 1) (i : Fin m) :
      inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i))
        (h1Coordinates (correctedOneElectronState hfreq u c) (Sum.inl s)) = c s i := by
    rw [correctedOneElectronState_coordinate]
    exact ho.inner_right_sum (c s) (Finset.mem_univ i)
  have he := corrected_complex_cross_expansion hfreq u c V hV B E hB
    (correctedOneElectronState hfreq u c)
  simp only [hi,mul_add,Finset.sum_add_distrib] at he
  have hnorm (z : ℂ) : (starRingEnd ℂ) z*z = (‖z‖^2 : ℝ) := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  have hm : (∑ s, ∑ i, (starRingEnd ℂ) (c s i)*((E:ℂ)*c s i)) =
      (E*Coulomb.mass (correctedOneElectronState hfreq u c) : ℝ) := by
    rw [correctedOneElectronState_mass hfreq u hsep hs c]
    push_cast
    simp_rw [show ∀ z : ℂ, (starRingEnd ℂ) z*((E:ℂ)*z) = (E:ℂ)*((starRingEnd ℂ) z*z) by
      intro z; ring,hnorm]
    simp only [← Finset.mul_sum]
    push_cast
    rfl
  rw [hm] at he
  have hre := congrArg Complex.re he
  have hself : graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates (correctedOneElectronState hfreq u c))
      (h1Coordinates (correctedOneElectronState hfreq u c)) =
      boundedPotentialForm V (correctedOneElectronState hfreq u c) := by
    rw [boundedPotentialForm_eq_graph V hV B hB]
    simp only [graphBoundedCross,graphBoundedForm,graphKinetic,real_inner_self_eq_norm_sq]
  rw [← graphBoundedCross_eq_re,hself] at hre
  simp only [Complex.add_re,Complex.ofReal_re] at hre
  linarith

theorem corrected_diagonal_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (hε : 0 ≤ ε) (herr : 4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) ≤ ε^2)
    (c : SpinConfiguration 1 → Fin m → ℂ) :
    (((-1/2:ℝ)+freq/2)-ε)*Coulomb.mass (correctedOneElectronState hfreq u c) ≤
      boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) (correctedOneElectronState hfreq u c) := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hV := (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
    oneElectronCoordinates.continuous
  have hi := corrected_diagonal_residual_identity hfreq u hsep hs c _ hV B
    ((-1/2:ℝ)+freq/2) (fun x => hB (oneElectronCoordinates x))
  simp only [Function.comp_def] at hi
  have hb := corrected_residual_sum_square_bound hdensity hrho hH hS hfreq hrelation
    hR hRH hRS scale u hsep hs hδ hcoeff c (correctedOneElectronState hfreq u c)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right herr (Coulomb.mass_nonneg _)) (Coulomb.mass_nonneg _))
  have hreal : (boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
      (oneElectronCoordinates x)) (correctedOneElectronState hfreq u c)-
      ((-1/2:ℝ)+freq/2)*Coulomb.mass (correctedOneElectronState hfreq u c))^2 ≤
      ε^2*Coulomb.mass (correctedOneElectronState hfreq u c)*
        Coulomb.mass (correctedOneElectronState hfreq u c) := by
    rw [hi]
    apply le_trans _ hb'
    rw [complex_norm_sq_parts]
    nlinarith only [sq_nonneg ((∑ s, ∑ i, (starRingEnd ℂ) (c s i)*
      realOrbitalPairing (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) ((-1/2:ℝ)+freq/2) (oneElectronCorrectedMode freq u i)
          (correctedOneElectronState hfreq u c) s).im)]
  have hn : 0 ≤ ε*Coulomb.mass (correctedOneElectronState hfreq u c) :=
    mul_nonneg hε (Coulomb.mass_nonneg _)
  nlinarith only [hreal,hn]

end ContinuumCoulomb

end

end OAI
