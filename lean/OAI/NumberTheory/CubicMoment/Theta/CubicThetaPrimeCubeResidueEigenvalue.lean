import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRadialResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLongWindowKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSelfAdjoint
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeWeakEquation

namespace OAI

/-! The actual arithmetic residue is a cubed-prime Hecke eigenvector.
The proof uses its two computed moments and self-adjointness. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSelfAdjoint_two_moments {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E)
    (hsym : ∀ u v, inner ℂ u (T v)=inner ℂ (T u) v)
    (R : E) (lam : ℂ) (hlam : star lam=lam)
    (h1 : inner ℂ (T R) R=lam*inner ℂ R R)
    (h2 : inner ℂ (T (T R)) R=lam^2*inner ℂ R R) : T R=lam • R := by
  have h1' : inner ℂ R (T R)=lam*inner ℂ R R :=
    (hsym R R).trans h1
  have h2' : inner ℂ (T R) (T R)=lam^2*inner ℂ R R :=
    (hsym (T R) R).trans h2
  have hs1 : inner ℂ (T R) (lam • R)=lam*inner ℂ (T R) R :=
    inner_smul_right (𝕜:=ℂ) (E:=E) (T R) R lam
  have hs2 : inner ℂ (lam • R) (T R)=lam*inner ℂ R (T R) := by
    simpa only [starRingEnd_apply,hlam] using
      (inner_smul_left (𝕜:=ℂ) (E:=E) R (T R) lam)
  have hs3 : inner ℂ (lam • R) (lam • R)=lam^2*inner ℂ R R := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=E),
      inner_smul_right (𝕜:=ℂ) (E:=E)]
    simp only [starRingEnd_apply,hlam]
    ring
  have hz : inner ℂ (T R-lam • R) (T R-lam • R)=0 := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hs1,hs2,hs3,h1,h1',h2']
    ring
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp hz)


theorem cubicThetaArithmeticResidueEnergy_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeEnergy hp (cubicThetaArithmeticResidueEnergy (4/3))=
      ((norm p)^2+norm p:ℂ) • cubicThetaArithmeticResidueEnergy (4/3) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1≤r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0<r := by linarith
  let H := 2*r^2
  have hH : 2≤H := by dsimp [H]; nlinarith
  let W := cubicThetaLongForcingWeight H (by linarith) (4/3)
  let V := cubicThetaRadialHeckeWeight r hr W
  let R := cubicThetaArithmeticResidueEnergy (4/3)
  let T := cubicThetaPrimeCubeHeckeEnergy hp
  let lam : ℂ := (norm p)^2+norm p
  have hlam : star lam=lam := by
    have he : lam=(((norm p)^2+norm p:ℝ):ℂ) := by
      dsimp only [lam]
      push_cast
      rfl
    rw [he]
    exact Complex.conj_ofReal _
  have hW : ∀ v≤2*r, W v=0 := by
    intro v hv
    apply cubicThetaLongForcingWeight_low
    change v≤2*r^2
    nlinarith
  have hV : ∀ v≤2*r, V v=0 := by
    apply cubicThetaRadialHeckeWeight_low hr1 (by positivity)
    intro v hv
    apply cubicThetaLongForcingWeight_low
    change v≤2*r^2
    nlinarith
  let obs : cubicThetaGlobalEnergySpace → ℂ := fun u =>
    inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaCuspRestriction u)
  have ho1 : obs (T R)=lam*obs R :=
    cubicThetaPrimeCube_residue_radial_observation hp W hW
  have ho2 : obs (T (T R))=lam^2*obs R := by
    change inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaCuspRestriction (T (T R)))=_
    rw [cubicThetaPrimeCubeRadialPairing_energy hp (T R) W hW]
    change inner ℂ (cubicThetaCuspFourierTest 0 V) (cubicThetaCuspRestriction (T R))=_
    rw [cubicThetaPrimeCube_residue_radial_observation hp V hV]
    change lam*inner ℂ (cubicThetaCuspFourierTest 0 V) (cubicThetaCuspRestriction R)=_
    rw [←cubicThetaPrimeCubeRadialPairing_energy hp R W hW]
    change lam*obs (T R)=_
    rw [ho1]
    ring
  have hR : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) R=0 := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using cubicThetaArithmeticResidueEnergy_kernel (4/3)
  have hTR := cubicThetaPrimeCubeHeckeEnergy_kernel hp _ R hR
  have hTTR := cubicThetaPrimeCubeHeckeEnergy_kernel hp _ (T R) hTR
  have hpair (u : cubicThetaGlobalEnergySpace)
      (hu : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) u=0) :
      inner ℂ u R=(17/6:ℂ)*star (obs u) :=
    cubicThetaResidue_long_kernel_pairing H hH u hu
  have h1 : inner ℂ (T R) R=lam*inner ℂ R R := by
    rw [hpair _ hTR,hpair _ hR,ho1,star_mul,hlam]
    ring
  have h2 : inner ℂ (T (T R)) R=lam^2*inner ℂ R R := by
    rw [hpair _ hTTR,hpair _ hR,ho2,star_mul,star_pow,hlam]
    ring
  exact cubicThetaSelfAdjoint_two_moments T (cubicThetaPrimeCubeHecke_symmetric hp) R lam hlam h1 h2

end CubicFirstMoment

end

end OAI
