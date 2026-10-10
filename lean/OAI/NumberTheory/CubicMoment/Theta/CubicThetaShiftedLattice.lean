import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedModelSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFrequency

namespace OAI

/-! Put the translated-cusp coefficients on the common lambda^-4 lattice.
The congruence restriction forces the apparent larger lattice to collapse. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShifted_support_lambda {n h : Eisenstein}
    (hh : (3:Eisenstein) ∣ h-lambdaE*n) : lambdaE ∣ h := by
  have ht : lambdaE ∣ (3:Eisenstein) := ⟨-lambdaE,by
    rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
  have ha := dvd_add (dvd_trans ht hh) (dvd_mul_right lambdaE n)
  simpa only [sub_add_cancel] using ha

lemma cubicThetaShifted_support_cancel (n k : Eisenstein) :
    (3:Eisenstein) ∣ lambdaE*k-lambdaE*n ↔ lambdaE ∣ k-n := by
  rw [←mul_sub]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨-a,?_⟩
    apply mul_left_cancel₀ lambdaE_prime.ne_zero
    rw [ha]
    rw [show lambdaE*(lambdaE*(-a))= -(lambdaE^2)*a by ring,lambdaE_sq]
    ring
  · rintro ⟨a,ha⟩
    refine ⟨-a,?_⟩
    rw [ha,←mul_assoc,←pow_two,lambdaE_sq]
    ring

lemma cubicThetaShiftedFrequency_common (k : Eisenstein) :
    cubicThetaShiftedRowFrequency (lambdaE*k)=cubicThetaFrequency k := by
  rw [cubicThetaFrequency_div_nine]
  unfold cubicThetaShiftedRowFrequency
  rw [Subalgebra.coe_mul,lambdaE_coe]
  field_simp [traceLambda_ne_zero]

/-- The actual translated-cusp coefficient, with the single global residue
scalar removed. This is derived, not postulated as a new theta family. -/
def cubicThetaShiftedLatticeCoefficient (n : ℤ) (k : Eisenstein) : ℂ :=
  if lambdaE ∣ k-(n:Eisenstein) then 3*cubicThetaArithmeticCoefficient (3*(lambdaE*k)) else 0

lemma cubicThetaShiftedLatticeCoefficient_bound (n : ℤ) (k : Eisenstein) :
    ‖cubicThetaShiftedLatticeCoefficient n k‖≤243 := by
  unfold cubicThetaShiftedLatticeCoefficient
  split_ifs
  · rw [norm_mul,Complex.norm_ofNat]
    calc
      _ ≤ 3*81 := mul_le_mul_of_nonneg_left (cubicThetaArithmeticCoefficient_norm_le _) (by norm_num)
      _ = _ := by norm_num
  · norm_num

lemma cubicThetaShiftedNormalizedCoefficient_common (n : ℤ) {k : Eisenstein} (hk : k≠0) :
    cubicThetaShiftedNormalizedCoefficient n (lambdaE*k)=
      cubicThetaArithmeticBaseScalar*cubicThetaShiftedLatticeCoefficient n k := by
  rw [cubicThetaShiftedNormalizedCoefficient_explicit n (mul_ne_zero lambdaE_prime.ne_zero hk),
    cubicThetaShifted_support_cancel]
  unfold cubicThetaShiftedLatticeCoefficient
  split_ifs <;> ring

lemma cubicThetaShiftedModelTerm_support (n : ℤ) (z : ℂ) (v : ℝ) :
    Function.support (fun h => cubicThetaShiftedModelTerm n v h*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)) ⊆
        Set.range (fun k : Eisenstein => lambdaE*k) := by
  intro h hh
  change cubicThetaShiftedModelTerm n v h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)≠0 at hh
  have hz : h≠0 := by
    rintro rfl
    exact hh (by simp only [cubicThetaShiftedModelTerm,ite_true,zero_mul])
  have hs : (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) := by
    by_contra hn
    exact hh (by simp only [cubicThetaShiftedModelTerm,ite_eq_right hz,
      cubicThetaShiftedNormalizedCoefficient_explicit n hz,ite_eq_right hn,zero_mul])
  obtain ⟨k,hk⟩ := cubicThetaShifted_support_lambda hs
  exact ⟨k,hk.symm⟩

lemma cubicThetaShiftedModelTerm_common (n : ℤ) (z : ℂ) (v : ℝ) (k : Eisenstein) :
    cubicThetaShiftedModelTerm n v (lambdaE*k)*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency (lambdaE*k))):ℂ)=
        cubicThetaArithmeticBaseScalar*cubicThetaSeriesTerm
          (cubicThetaShiftedLatticeCoefficient n) z v k := by
  by_cases hk : k=0
  · subst k
    simp only [mul_zero,cubicThetaShiftedModelTerm,cubicThetaSeriesTerm,ite_true,zero_mul]
  · simp only [cubicThetaShiftedModelTerm,cubicThetaSeriesTerm,
      ite_eq_right (mul_ne_zero lambdaE_prime.ne_zero hk),ite_eq_right hk,
      cubicThetaShiftedNormalizedCoefficient_common n hk,cubicThetaShiftedFrequency_common]
    have ht : tracePair z (cubicThetaFrequency k)=tracePair (cubicThetaFrequency k) z := by
      exact congrArg (fun w : ℂ => 2*w.re) (mul_comm z (cubicThetaFrequency k))
    rw [ht]
    ring

theorem cubicThetaShiftedModelSeries_common (n : ℤ) (z : ℂ) (v : ℝ) :
    cubicThetaShiftedModelSeries n z v=cubicThetaArithmeticBaseScalar*
      cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) (z,v) := by
  have hinj : Function.Injective (fun k : Eisenstein => lambdaE*k) :=
    fun _ _ he => mul_left_cancel₀ lambdaE_prime.ne_zero he
  have he := hinj.tsum_eq (cubicThetaShiftedModelTerm_support n z v)
  rw [cubicThetaShiftedModelSeries,←he]
  simp_rw [cubicThetaShiftedModelTerm_common]
  exact tsum_mul_left

end CubicFirstMoment

end

end OAI
