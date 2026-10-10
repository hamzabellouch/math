import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWirtinger
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedSeries

namespace OAI

/-! Every signed angular series is an actual iterated horizontal derivative.
The constant Fourier mode disappears after the first derivative. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngularCoefficient_zero (a : Eisenstein → ℂ) :
    cubicThetaAngularCoefficient a 0=a := by
  funext n
  simp [cubicThetaAngularCoefficient]

lemma cubicThetaWirtingerPositive_const_add (A : ℂ) (f : ℂ → ℂ) :
    cubicThetaWirtingerPositive (fun z => A+f z)=cubicThetaWirtingerPositive f := by
  funext z
  simp only [cubicThetaWirtingerPositive,deriv_const_add]

lemma cubicThetaWirtingerNegative_const_add (A : ℂ) (f : ℂ → ℂ) :
    cubicThetaWirtingerNegative (fun z => A+f z)=cubicThetaWirtingerNegative f := by
  funext z
  simp only [cubicThetaWirtingerNegative,deriv_const_add]

theorem cubicThetaWirtingerPositive_iterate {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hv : 0<v) (k : ℕ) :
    (cubicThetaWirtingerPositive^[k]) (fun z => cubicThetaNonconstant a (z,v))=
      fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (k:ℤ)) (z,v) := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.cast_zero,cubicThetaAngularCoefficient_zero]
  | succ k ih =>
      rw [Function.iterate_succ_apply',ih]
      funext z
      exact cubicThetaWirtingerPositive_angular hC ha k hv z

theorem cubicThetaWirtingerNegative_iterate {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hv : 0<v) (k : ℕ) :
    (cubicThetaWirtingerNegative^[k]) (fun z => cubicThetaNonconstant a (z,v))=
      fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (-(k:ℤ))) (z,v) := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.cast_zero,neg_zero,cubicThetaAngularCoefficient_zero]
  | succ k ih =>
      rw [Function.iterate_succ_apply',ih]
      funext z
      exact cubicThetaWirtingerNegative_angular hC ha k hv z

theorem cubicThetaWirtingerPositive_iterate_const {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hv : 0<v) (A : ℂ) {k : ℕ} (hk : 0<k) :
    (cubicThetaWirtingerPositive^[k]) (fun z => A+cubicThetaNonconstant a (z,v))=
      fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (k:ℤ)) (z,v) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Function.iterate_succ_apply,cubicThetaWirtingerPositive_const_add,
    ←Function.iterate_succ_apply]
  exact cubicThetaWirtingerPositive_iterate hC ha hv (j+1)

theorem cubicThetaWirtingerNegative_iterate_const {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hv : 0<v) (A : ℂ) {k : ℕ} (hk : 0<k) :
    (cubicThetaWirtingerNegative^[k]) (fun z => A+cubicThetaNonconstant a (z,v))=
      fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (-(k:ℤ))) (z,v) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Function.iterate_succ_apply,cubicThetaWirtingerNegative_const_add,
    ←Function.iterate_succ_apply]
  exact cubicThetaWirtingerNegative_iterate hC ha hv (j+1)

end CubicFirstMoment

end

end OAI
