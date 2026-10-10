import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.MovingWells
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronTrial

namespace OAI

/-!
# Stability of the unrestricted isolated-well variational bottom

All infima range over normalized spinful weak-H¹ states. The estimates use
form comparison and a concrete normalized bump trial; no eigenfunction, attainment, or
spectral oracle is supplied as an assumption.
-/

noncomputable section
namespace ContinuumCoulomb

def oneElectronEnergy (form : Coulomb.H1Vector 1 → ℝ) : EReal :=
  sInf {e | ∃ state : Coulomb.H1Vector 1,
    Coulomb.mass state = 1 ∧ e = (form state : EReal)}

def hydrogenEnergy (a : Position) : EReal := oneElectronEnergy (hydrogenForm a)

def isolatedWellEnergy {m : ℕ} (D q q' : ℝ) (center displacement : Fin m → Position)
    (site : Fin m) : EReal := oneElectronEnergy (isolatedWellForm D q q' center displacement site)

theorem oneElectronEnergy_le_trial (form : Coulomb.H1Vector 1 → ℝ)
    (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
    oneElectronEnergy form ≤ (form state : EReal) :=
  sInf_le ⟨state, hnorm, rfl⟩

theorem oneElectronEnergy_lower_of_forall (form : Coulomb.H1Vector 1 → ℝ) (a : ℝ)
    (ha : ∀ state : Coulomb.H1Vector 1, Coulomb.mass state = 1 → a ≤ form state) :
    (a : EReal) ≤ oneElectronEnergy form := by
  apply le_sInf
  rintro e ⟨state, hnorm, rfl⟩
  exact EReal.coe_le_coe (ha state hnorm)

theorem oneElectronEnergy_finite (form : Coulomb.H1Vector 1 → ℝ)
    (trial : Coulomb.H1Vector 1) (htrial : Coulomb.mass trial = 1) (a : ℝ)
    (ha : ∀ state : Coulomb.H1Vector 1, Coulomb.mass state = 1 → a ≤ form state) :
    oneElectronEnergy form ≠ ⊤ ∧ oneElectronEnergy form ≠ ⊥ := by
  exact ⟨ne_of_lt ((oneElectronEnergy_le_trial form trial htrial).trans_lt
    (EReal.coe_lt_top _)),
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (oneElectronEnergy_lower_of_forall form a ha))⟩

theorem hydrogenEnergy_finite (a : Position) : hydrogenEnergy a ≠ ⊤ ∧ hydrogenEnergy a ≠ ⊥ := by
  apply oneElectronEnergy_finite (hydrogenForm a) oneElectronTrial oneElectronTrial_mass (-4)
  intro state hnorm
  have h := hydrogenForm_coercive a state
  rw [hnorm] at h
  linarith [Coulomb.kinetic_nonneg state]

theorem isolatedWellEnergy_finite {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) :
    isolatedWellEnergy D q q' center displacement site ≠ ⊤ ∧
      isolatedWellEnergy D q q' center displacement site ≠ ⊥ := by
  apply oneElectronEnergy_finite _ oneElectronTrial oneElectronTrial_mass (-(16 + 48 * m / D))
  intro state hnorm
  have h := isolatedWellForm_coercive hD hq hq1 hq' hq'1
    center displacement hdisp site state
  rw [hnorm] at h
  linarith [Coulomb.kinetic_nonneg state]

theorem oneElectronEnergy_bounded_perturbation (f g : Coulomb.H1Vector 1 → ℝ)
    (hf : oneElectronEnergy f ≠ ⊤ ∧ oneElectronEnergy f ≠ ⊥)
    (hg : oneElectronEnergy g ≠ ⊤ ∧ oneElectronEnergy g ≠ ⊥) (delta : ℝ)
    (herror : ∀ state : Coulomb.H1Vector 1, Coulomb.mass state = 1 →
      |g state - f state| ≤ delta) :
    |(oneElectronEnergy g).toReal - (oneElectronEnergy f).toReal| ≤ delta := by
  have hfc : ((oneElectronEnergy f).toReal : EReal) = oneElectronEnergy f :=
    EReal.coe_toReal hf.1 hf.2
  have hgc : ((oneElectronEnergy g).toReal : EReal) = oneElectronEnergy g :=
    EReal.coe_toReal hg.1 hg.2
  have hfl (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
      (oneElectronEnergy f).toReal ≤ f state := by
    apply EReal.coe_le_coe_iff.mp
    rw [hfc]
    exact oneElectronEnergy_le_trial f state hnorm
  have hgl (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
      (oneElectronEnergy g).toReal ≤ g state := by
    apply EReal.coe_le_coe_iff.mp
    rw [hgc]
    exact oneElectronEnergy_le_trial g state hnorm
  have hl : (oneElectronEnergy f).toReal - delta ≤ (oneElectronEnergy g).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [hgc]
    apply oneElectronEnergy_lower_of_forall
    intro state hnorm
    have h := (abs_le.mp (herror state hnorm)).1
    linarith [hfl state hnorm]
  have hu : (oneElectronEnergy g).toReal - delta ≤ (oneElectronEnergy f).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [hfc]
    apply oneElectronEnergy_lower_of_forall
    intro state hnorm
    have h := (abs_le.mp (herror state hnorm)).2
    linarith [hgl state hnorm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem isolatedWellEnergy_relative {m : ℕ} {D q q' epsilon : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hprimary : |1 - q| ≤ epsilon) (hsecondary : q' ≤ epsilon)
    (hbackground : 48 * m / D ≤ epsilon) (hsmall : 10 * epsilon ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) :
    |(isolatedWellEnergy D q q' center displacement site).toReal -
      (hydrogenEnergy (center site)).toReal| ≤
        10 * epsilon * ((hydrogenEnergy (center site)).toReal + 5) := by
  let E := (hydrogenEnergy (center site)).toReal
  let F := (isolatedWellEnergy D q q' center displacement site).toReal
  let theta := 10 * epsilon
  have hepsilon : 0 ≤ epsilon := hq'.trans hsecondary
  have htheta : 0 ≤ theta := by dsimp [theta]; positivity
  have hslower : 0 ≤ 1 - theta := by dsimp [theta]; linarith
  have hsupper : 0 < 1 + theta := by linarith
  have hEcoe : (E : EReal) = hydrogenEnergy (center site) :=
    EReal.coe_toReal (hydrogenEnergy_finite (center site)).1
      (hydrogenEnergy_finite (center site)).2
  have hFcoe : (F : EReal) = isolatedWellEnergy D q q' center displacement site :=
    EReal.coe_toReal (isolatedWellEnergy_finite hD hq hq1 hq' hq'1
      center displacement hdisp site).1
      (isolatedWellEnergy_finite hD hq hq1 hq' hq'1
        center displacement hdisp site).2
  have hEtrial (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
      E ≤ hydrogenForm (center site) state := by
    apply EReal.coe_le_coe_iff.mp
    rw [hEcoe]
    exact oneElectronEnergy_le_trial _ state hnorm
  have hFtrial (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
      F ≤ isolatedWellForm D q q' center displacement site state := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    exact oneElectronEnergy_le_trial _ state hnorm
  have hpoint (state : Coulomb.H1Vector 1) (hnorm : Coulomb.mass state = 1) :
      (1 - theta) * hydrogenForm (center site) state - 5 * theta ≤
        isolatedWellForm D q q' center displacement site state ∧
      isolatedWellForm D q q' center displacement site state ≤
        (1 + theta) * hydrogenForm (center site) state + 5 * theta := by
    have h := isolatedWellForm_relative hD hq hq1 hq' hq'1 hprimary hsecondary hbackground
      center displacement hdisp site state
    rw [hnorm] at h
    change |_ - _| ≤ theta * (_ + 5 * 1) at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> nlinarith
  have hl : (1 - theta) * E - 5 * theta ≤ F := by
    apply EReal.coe_le_coe_iff.mp
    rw [hFcoe]
    apply oneElectronEnergy_lower_of_forall
    intro state hnorm
    have h := mul_le_mul_of_nonneg_left (hEtrial state hnorm) hslower
    linarith [(hpoint state hnorm).1]
  have hu : F ≤ (1 + theta) * E + 5 * theta := by
    have haux : (F - 5 * theta) / (1 + theta) ≤ E := by
      apply EReal.coe_le_coe_iff.mp
      rw [hEcoe]
      apply oneElectronEnergy_lower_of_forall
      intro state hnorm
      apply (div_le_iff₀ hsupper).2
      have h := hFtrial state hnorm
      nlinarith [(hpoint state hnorm).2]
    have h := (div_le_iff₀ hsupper).mp haux
    nlinarith
  change |F - E| ≤ theta * (E + 5)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Keeping the own secondary nucleus fixed yields the small other-site
energy Lipschitz bound on the actual infimum, without a ground-state premise. -/
theorem isolatedWellEnergy_other_displacements {m : ℕ} {D q q' delta : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hdelta : 0 ≤ delta) (center a b : Fin m → Position)
    (ha : ∀ j, ‖a j‖ ≤ 4) (hb : ∀ j, ‖b j‖ ≤ 4)
    (hmove : ∀ j, ‖a j - b j‖ ≤ delta) (site : Fin m) (hown : a site = b site) :
    |(isolatedWellEnergy D q q' center b site).toReal -
      (isolatedWellEnergy D q q' center a site).toReal| ≤ 2048 * q' * m / D ^ 2 * delta := by
  apply oneElectronEnergy_bounded_perturbation _ _
    (isolatedWellEnergy_finite hD hq hq1 hq' hq'1 center a ha site)
    (isolatedWellEnergy_finite hD hq hq1 hq' hq'1 center b hb site)
  intro state hnorm
  have h := isolatedWellForm_displacement_bound hD hq hq1 hq' hq'1 hdelta
    center a b ha hb hmove site state
  rw [hown, sub_self, norm_zero, mul_zero, zero_mul, zero_add, hnorm, mul_one] at h
  simpa only [abs_sub_comm] using h

end ContinuumCoulomb

end

end OAI
