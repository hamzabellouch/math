import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteFourierInverse
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanExactEnergy

namespace OAI

/-! The finite projection selected by the actual primary-unit cubic
weight. Its image and its relation to Kloosterman energy are exact. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimaryMultiplier (c : Eisenstein) (f : Residues (3*c) → ℂ)
    (x : Residues (3*c)) : ℂ :=
  if IsUnit x ∧ cubicThetaReductionThree c x=1 then f x else 0

def cubicThetaFinitePrimaryProjection (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (x : Residues (3*c)) : ℂ :=
  (Fintype.card (Residues (3*c)):ℂ)⁻¹*
    cubicThetaFiniteFourierAdjoint (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaPrimaryMultiplier c
        (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f)) x

theorem cubicThetaFinitePrimaryProjection_fourier (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (x : Residues (3*c)) :
    cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaFinitePrimaryProjection c hc0 f) x=
      cubicThetaPrimaryMultiplier c
        (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f) x := by
  have hn : (Fintype.card (Residues (3*c)):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Residues (3*c)))).ne'
  unfold cubicThetaFinitePrimaryProjection
  rw [cubicThetaFiniteFourier_const_mul,cubicThetaFiniteFourier_inverse_adjoint,
    ←mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem cubicThetaFinitePrimaryProjection_idempotent (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    cubicThetaFinitePrimaryProjection c hc0 (cubicThetaFinitePrimaryProjection c hc0 f)=
      cubicThetaFinitePrimaryProjection c hc0 f := by
  apply cubicThetaFiniteFourier_injective (3*c) (mul_ne_zero (by norm_num) hc0)
  funext x
  simp only [cubicThetaFinitePrimaryProjection_fourier,cubicThetaPrimaryMultiplier]
  split_ifs <;> rfl

theorem cubicThetaFinitePrimaryProjection_fixed_iff (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    cubicThetaFinitePrimaryProjection c hc0 f=f ↔
      ∀ x : Residues (3*c),¬(IsUnit x ∧ cubicThetaReductionThree c x=1) →
        cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f x=0 := by
  constructor
  · intro he x hx
    have hF := cubicThetaFinitePrimaryProjection_fourier c hc0 f x
    rw [he] at hF
    simpa only [cubicThetaPrimaryMultiplier,ite_eq_right hx] using hF
  · intro he
    apply cubicThetaFiniteFourier_injective (3*c) (mul_ne_zero (by norm_num) hc0)
    funext x
    rw [cubicThetaFinitePrimaryProjection_fourier]
    unfold cubicThetaPrimaryMultiplier
    split_ifs with hx
    · rfl
    · exact (he x hx).symm

theorem cubicThetaFinitePrimaryProjection_energy (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (Fintype.card (Residues (3*c)):ℝ)*
      (∑ x : Residues (3*c),‖cubicThetaFinitePrimaryProjection c hc0 f x‖^2)=
      ∑ x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then
        ‖cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f x‖^2 else 0 := by
  rw [←cubicThetaFiniteFourier_norm_sq (3*c) (mul_ne_zero (by norm_num) hc0)
    (cubicThetaFinitePrimaryProjection c hc0 f)]
  apply Finset.sum_congr rfl
  intro x _
  rw [cubicThetaFinitePrimaryProjection_fourier]
  unfold cubicThetaPrimaryMultiplier
  split_ifs <;> simp

theorem cubicThetaFiniteKloostermanApply_projection_energy (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (∑ h : Residues (3*c),‖cubicThetaFiniteKloostermanApply c hc0 f h‖^2)=
      (Fintype.card (Residues (3*c)):ℝ)^2*
        (∑ x : Residues (3*c),‖cubicThetaFinitePrimaryProjection c hc0 f x‖^2) := by
  rw [cubicThetaFiniteKloostermanApply_energy c hc0 f,
    ←cubicThetaFinitePrimaryProjection_energy c hc0 f]
  ring

end CubicFirstMoment

end

end OAI
