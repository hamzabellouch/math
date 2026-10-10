import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ElectronSlotBound

namespace OAI

/-! The core occupation depends only on the L2 state. A global phase and
fermionic coordinate permutations preserve it. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem coreOrbitalCoefficient_phase_ae {n : ℕ} (u v : Coulomb.H1Vector (n+1))
    (c : ℂ) (h : ∀ s, u.value s =ᵐ[volume] fun x => c*v.value s x)
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) :
    coreOrbitalCoefficient u φ s t =ᵐ[volume]
      fun x => c*coreOrbitalCoefficient v φ s t x := by
  have hp := (Coulomb.joinConfiguration_measurePreserving n 1).quasiMeasurePreserving.ae
    (h (Fin.append s t))
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with x hx
  unfold coreOrbitalCoefficient
  calc
    _ = ∫ y, c*(star (φ y)*v.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y))) := by
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      change u.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y)) =
        c*v.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y)) at hy
      rw [hy]
      ring
    _ = _ := integral_const_mul _ _

theorem coreOrbitalMass_phase {n : ℕ} {ι : Type*} [Fintype ι]
    (u v : Coulomb.H1Vector (n+1)) (c : ℂ) (hc : ‖c‖=1)
    (h : ∀ s, u.value s =ᵐ[volume] fun x => c*v.value s x)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass u φ = coreOrbitalMass v φ := by
  rw [coreOrbitalMass_eq_coefficients,coreOrbitalMass_eq_coefficients]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [coreOrbitalCoefficient_phase_ae u v c h (φ i) s t] with x hx
  rw [hx,norm_mul,hc,one_mul]

theorem coreOrbitalMass_permutation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (p : Equiv.Perm (Fin (n+1)))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass (u.permutation p) φ = coreOrbitalMass u φ := by
  apply coreOrbitalMass_phase _ _ ((p.sign : ℤ):ℂ) (Coulomb.sign_complex_norm p)
  intro s
  filter_upwards [hu p s] with x hx
  rw [Coulomb.permutation_value,hx]

theorem totalOrbitalMass_antisymmetric {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    totalOrbitalMass u φ = (n+1:ℕ)*coreOrbitalMass u φ := by
  unfold totalOrbitalMass electronSlotOrbitalMass
  simp_rw [coreOrbitalMass_permutation u hu]
  simp

end ContinuumCoulomb

end

end OAI
