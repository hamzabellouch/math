import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Laplacian
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1PairingBound

namespace OAI

/-! Weak form of a real one-electron orbital's differential residual.
This is used for finite corrected combinations of the manufactured modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def realOrbitalPairing (V : Configuration 1 → ℝ) (E : ℝ)
    (φ : Configuration 1 → ℝ) (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) : ℂ :=
  (1/2:ℂ)*(∑ a, ∫ x, v.gradient s a x*(configurationRealPartial φ a x : ℂ))+
    (∫ x, v.value s x*(V x*φ x : ℝ))-(E:ℂ)*(∫ x, v.value s x*(φ x : ℂ))

theorem realOrbitalPairing_eq_residual (hdensity : PublishedSobolevSmoothDensity)
    (V : Configuration 1 → ℝ) (E : ℝ) (φ R : Configuration 1 → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hm : MemLp φ 2)
    (hp : ∀ a, MemLp (configurationRealPartial φ a) 2)
    (hV : MemLp (fun x => V x*φ x) 2) (hR : MemLp R 2)
    (heq : ∀ x, R x = -(1/2:ℝ)*configurationRealLaplacian φ x+V x*φ x-E*φ x)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    realOrbitalPairing V E φ v s = ∫ x, v.value s x*(R x : ℂ) := by
  have hL : MemLp (configurationRealLaplacian φ) 2 := by
    have he : configurationRealLaplacian φ = (fun x => 2*(V x*φ x-E*φ x-R x)) := by
      funext x
      linarith [heq x]
    rw [he]
    exact ((hV.sub (hm.const_mul E)).sub hR).const_mul 2
  have hi := weakH1_laplacian_pairing hdensity φ hφ hp hL v s
  have hLI := (v.value_L2 s).integrable_mul hL.ofReal
  have hVI := (v.value_L2 s).integrable_mul hV.ofReal
  have hPI := (v.value_L2 s).integrable_mul hm.ofReal
  have he (x : Configuration 1) : v.value s x*(R x : ℂ) =
      (-1/2:ℂ)*(v.value s x*(configurationRealLaplacian φ x : ℂ))+
      v.value s x*(V x*φ x : ℝ)-(E:ℂ)*(v.value s x*(φ x : ℂ)) := by
    rw [heq x]
    push_cast
    ring
  unfold realOrbitalPairing
  simp_rw [he]
  have hsub := integral_sub ((hLI.const_mul (-1/2:ℂ)).add hVI) (hPI.const_mul (E:ℂ))
  have hadd := integral_add (hLI.const_mul (-1/2:ℂ)) hVI
  simp only [Pi.add_apply,Pi.mul_apply] at hsub hadd
  rw [hadd,integral_const_mul,integral_const_mul] at hsub
  rw [hi]
  let A : ℂ := ∫ x, v.value s x*(configurationRealLaplacian φ x : ℂ)
  let B : ℂ := ∫ x, v.value s x*(V x*φ x : ℝ)
  let C : ℂ := ∫ x, v.value s x*(φ x : ℂ)
  change _ = (-1/2:ℂ)*A+B-(E:ℂ)*C at hsub
  change (1/2:ℂ)*(-A)+B-(E:ℂ)*C = _
  calc
    _ = (-1/2:ℂ)*A+B-(E:ℂ)*C := by ring
    _ = _ := hsub.symm

theorem realOrbitalPairing_square_bound (hdensity : PublishedSobolevSmoothDensity)
    (V : Configuration 1 → ℝ) (E : ℝ) (φ R : Configuration 1 → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hm : MemLp φ 2)
    (hp : ∀ a, MemLp (configurationRealPartial φ a) 2)
    (hV : MemLp (fun x => V x*φ x) 2) (hR : MemLp R 2)
    (heq : ∀ x, R x = -(1/2:ℝ)*configurationRealLaplacian φ x+V x*φ x-E*φ x)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    ‖realOrbitalPairing V E φ v s‖^2 ≤ (∫ x, R x^2)*(∫ x, ‖v.value s x‖^2) := by
  rw [realOrbitalPairing_eq_residual hdensity V E φ R hφ hm hp hV hR heq]
  exact h1_real_pairing_sq_le v s R hR

end ContinuumCoulomb

end

end OAI
