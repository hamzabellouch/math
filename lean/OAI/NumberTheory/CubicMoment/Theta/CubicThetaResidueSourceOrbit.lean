import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFourierOrbit
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueEigenvalue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeArithmeticResidue

namespace OAI

/-! The actual residue applied to the full positive-cutoff source orbit.
The scalar recurrence here is derived from its proved Hecke eigenvalue. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidueL2_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeMass hp cubicThetaArithmeticResidueL2=
      ((norm p)^2+norm p:ℂ) • cubicThetaArithmeticResidueL2 := by
  have he : cubicThetaArithmeticResidueL2=
      cubicThetaGlobalEnergyValueMap (cubicThetaArithmeticResidueEnergy (4/3)) := rfl
  rw [he,cubicThetaPrimeCubeHeckeMass_energy,cubicThetaArithmeticResidueEnergy_hecke,map_smul]

lemma cubicThetaResidueSourcePairing_hecke {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeHeckeMass hp u) cubicThetaArithmeticResidueL2=
      ((norm p)^2+norm p:ℂ)*inner ℂ u cubicThetaArithmeticResidueL2 := by
  rw [←cubicThetaPrimeCubeHeckeMass_symmetric,cubicThetaArithmeticResidueL2_hecke,
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2)]

def cubicThetaPrimeResidueOrbit {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (k : ℕ) : ℂ :=
  inner ℂ (cubicThetaPrimeFourierOrbit hp h W hε hW hsm k) cubicThetaArithmeticResidueL2

theorem cubicThetaPrimeResidueOrbit_step {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (k : ℕ) :
    cubicThetaPrimeResidueOrbit hp h W hε hW hsm (k+2)=
      ((norm p)^2+norm p:ℂ)*cubicThetaPrimeResidueOrbit hp h W hε hW hsm (k+1)-
        ((norm p:ℂ)^3)*cubicThetaPrimeResidueOrbit hp h W hε hW hsm k := by
  have he := congrArg (fun u => inner ℂ u cubicThetaArithmeticResidueL2)
    (cubicThetaPrimeFourierOrbit_step hp h W hε hW hsm k)
  rw [cubicThetaResidueSourcePairing_hecke,inner_add_left,
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2)] at he
  have hc : (starRingEnd ℂ) (((‖(p:ℂ)‖^3)^2:ℝ):ℂ)=
      (((‖(p:ℂ)‖^3)^2:ℝ):ℂ) := Complex.conj_ofReal _
  rw [hc] at he
  have hn : (((‖(p:ℂ)‖^3)^2:ℝ):ℂ)=(norm p:ℂ)^3 := by
    change _=(Complex.normSq (p:ℂ):ℂ)^3
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hn] at he
  change ((norm p)^2+norm p:ℂ)*cubicThetaPrimeResidueOrbit hp h W hε hW hsm (k+1)=
    ((norm p:ℂ)^3)*cubicThetaPrimeResidueOrbit hp h W hε hW hsm k+
    cubicThetaPrimeResidueOrbit hp h W hε hW hsm (k+2) at he
  linear_combination -he

lemma cubicThetaPrimeResidueOrbit_square_start {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeResidueOrbit hp (p^2*h) W hε hW hsm 1=
      ((norm p)^2+norm p:ℂ)*cubicThetaPrimeResidueOrbit hp (p^2*h) W hε hW hsm 0 := by
  unfold cubicThetaPrimeResidueOrbit
  rw [←cubicThetaPrimeFourierOrbit_square_start hp h hh W hε hW hsm,
    cubicThetaResidueSourcePairing_hecke]

theorem cubicThetaPrimeResidueOrbit_square_closed {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (k : ℕ) :
    ((norm p:ℂ)^2-(norm p:ℂ))*cubicThetaPrimeResidueOrbit hp (p^2*h) W hε hW hsm k=
      (((norm p:ℂ)^2)^(k+1)-(norm p:ℂ)^(k+1))*
        cubicThetaPrimeResidueOrbit hp (p^2*h) W hε hW hsm 0 := by
  let q : ℂ := norm p
  let a : ℕ → ℂ := cubicThetaPrimeResidueOrbit hp (p^2*h) W hε hW hsm
  change (q^2-q)*a k=((q^2)^(k+1)-q^(k+1))*a 0
  have ha0 : a 1=(q^2+q)*a 0 := cubicThetaPrimeResidueOrbit_square_start hp h hh W hε hW hsm
  have has (j : ℕ) : a (j+2)=(q^2+q)*a (j+1)-q^3*a j :=
    cubicThetaPrimeResidueOrbit_step hp (p^2*h) W hε hW hsm j
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => rw [ha0]; ring
  | more k ih0 ih1 =>
    rw [has]
    calc
      _ = (q^2+q)*((q^2-q)*a (k+1))-q^3*((q^2-q)*a k) := by ring
      _ = (q^2+q)*(((q^2)^(k+1+1)-q^(k+1+1))*a 0)-
          q^3*(((q^2)^(k+1)-q^(k+1))*a 0) := by rw [ih0,ih1]
      _ = _ := by simp only [pow_succ]; ring

end CubicFirstMoment

end

end OAI
