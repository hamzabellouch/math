import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierPhase

namespace OAI

/-! Exact action of the finite translation branches on a horizontal
Fourier mode with an arbitrary vertical profile. No spectral assertion
about the global residue is used here. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimeCubeFourierMode (h : Eisenstein) (f : ℝ → ℂ)
    (x : CubicThetaPoint) : ℂ :=
  (Real.fourierChar (tracePair x.val.1 (cubicThetaRowFrequency h)) : ℂ)*f x.val.2

def cubicThetaPrimeCubeScaledMode {p : Eisenstein} (_hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) : ℂ :=
  (Real.fourierChar (tracePair x.val.1
    ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*cubicThetaRowFrequency h)) : ℂ)*
      f ((‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*x.val.2)

lemma cubicThetaPrimeCubeFourierMode_branch {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h b : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFourierMode h f (cubicThetaPrimeCubeBranchPoint hp k b x)=
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) (h*b))*
          cubicThetaPrimeCubeScaledMode hp k h f x := by
  unfold cubicThetaPrimeCubeFourierMode cubicThetaPrimeCubeBranchPoint
    cubicThetaPrimeCubeScaledMode
  have h3 : ((3 : Eisenstein) : ℂ)=3 := map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3
  simp only [Subalgebra.coe_mul]
  rw [h3]
  rw [cubicThetaPrimeCubeFourierPhase hp]
  ring

def cubicThetaPrimeCubeUnitModeSum {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      cubicThetaPrimeCubeFourierMode h f (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) x)

theorem cubicThetaPrimeCubeUnitModeSum_eq {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeUnitModeSum hp k h f x=
      cubicThetaPrimeCubeUnitFourier hp k h*cubicThetaPrimeCubeScaledMode hp k h f x := by
  unfold cubicThetaPrimeCubeUnitModeSum cubicThetaPrimeCubeUnitFourier
  rw [←tsum_mul_right]
  apply tsum_congr
  intro u
  rw [cubicThetaPrimeCubeFourierMode_branch,map_mul,residueRepresentative_spec]
  ring

theorem cubicThetaPrimeCubeUnitModeSum_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) (hh : ¬p^(2-k.val)∣h)
    (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeUnitModeSum hp k h f x=0 := by
  rw [cubicThetaPrimeCubeUnitModeSum_eq,cubicThetaPrimeCubeUnitFourier_zero hp k hk h hh,
    zero_mul]

def cubicThetaPrimeCubeBottomFourier {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : ℂ :=
  ∑' r : Residues (p^3), residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
    (Ideal.Quotient.mk (modulus (p^3)) h*r)

lemma cubicThetaResidues_card_complex {q : Eisenstein} (hq : q≠0)
    [Fintype (Residues q)] : (Fintype.card (Residues q) : ℂ)=(norm q : ℂ) := by
  rw [←Nat.card_eq_fintype_card,residues_card hq]
  exact_mod_cast normNat_cast q

theorem cubicThetaPrimeCubeBottomFourier_eq {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaPrimeCubeBottomFourier hp h=if p^3∣h then (norm (p^3):ℂ) else 0 := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  unfold cubicThetaPrimeCubeBottomFourier
  rw [tsum_fintype]
  simp_rw [mul_comm (Ideal.Quotient.mk (modulus (p^3)) h)]
  rw [AddChar.sum_mulShift _ (residueFourierChar_isPrimitive _ _)]
  have he : Ideal.Quotient.mk (modulus (p^3)) h=0 ↔ p^3∣h := by
    rw [Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]
  rw [he]
  split_ifs
  · exact cubicThetaResidues_card_complex (pow_ne_zero 3 hp.2.ne_zero)
  · norm_num

end CubicFirstMoment

end

end OAI
