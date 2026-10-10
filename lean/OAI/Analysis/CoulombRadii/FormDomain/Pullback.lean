import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace Coulomb

lemma linear_form_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : EuclideanSpace ℝ ι) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul]

lemma H1Vector.weak_directional {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (v : Configuration n) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, (∑ a, (v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hcφ.comp_left (by simp))
  have hdφL (a : Fin n × Fin 3) :
      MemLp (fun x => (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hcφ.fderiv_apply ℝ _).comp_left (by simp))
  have Hd (x : Configuration n) := linear_form_eq_sum (fderiv ℝ φ x) v
  simp_rw [Hd, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul]
  have hA (a : Fin n × Fin 3) : Integrable (fun x => ψ.value s x *
      ((v a : ℂ) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ))) := by
    simpa only [Pi.mul_apply, mul_left_comm] using ((ψ.value_L2 s).integrable_mul (hdφL a)).const_mul (v a : ℂ)
  have hB (a : Fin n × Fin 3) : Integrable (fun x =>
      ((v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) :=
    by simpa only [Pi.mul_apply, mul_assoc] using ((ψ.partial_L2 s a).integrable_mul hφL).const_mul (v a : ℂ)
  rw [integral_finsetSum _ (fun a _ => hA a), integral_finsetSum _ (fun a _ => hB a),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [mul_left_comm (ψ.value s _) (v a : ℂ), mul_assoc]
  rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a φ hφ hcφ]
  ring

lemma H1Vector.weak_partial_isometry {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) (s : Spins n) (a : Fin n × Fin 3)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s (L x) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)) * (φ x : ℂ)) := by
  let Φ : Configuration n → ℝ := fun y => φ (L.symm y)
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hφ.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hcφ.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : Configuration n) : fderiv ℝ Φ y (L (EuclideanSpace.single a 1)) =
      fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) := by
    change fderiv ℝ (φ ∘ L.symm) y _ = _
    rw [fderiv_comp y (hφ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    rw [show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearEquiv.toContinuousLinearMap from
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    simp
  have H := ψ.weak_directional s (L (EuclideanSpace.single a 1)) Φ HΦ HC
  simp_rw [Hd] at H
  have mp : MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume := L.measurePreserving
  rw [← mp.integral_comp' (fun y => ψ.value s y *
      (fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) : ℂ)),
    ← mp.integral_comp' (fun y => (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) *
      ψ.gradient s k y) * (Φ y : ℂ))] at H
  simpa [Φ] using H

noncomputable def H1Vector.pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : H1Vector n where
  value := fun s x => ψ.value s (L x)
  gradient := fun s a x => ∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)
  value_L2 := fun s => (ψ.value_L2 s).comp_measurePreserving L.measurePreserving
  partial_L2 := fun s _a => memLp_finsetSum _ (fun k _ =>
    ((ψ.partial_L2 s k).comp_measurePreserving L.measurePreserving).const_mul _)
  weak_partial := ψ.weak_partial_isometry L

lemma isometry_complex_gradient_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (g : ι → ℂ) :
    (∑ a, ‖∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k‖^2) = ∑ k, ‖g k‖^2 := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => (g k).re)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => (g k).im)
  let b := (EuclideanSpace.basisFun ι ℝ).map L
  have hr (a : ι) : (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k).re =
      inner ℝ (b a) u := by
    simp [b, u, PiLp.inner_apply, Complex.mul_re, mul_comm]
  have hi (a : ι) : (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * g k).im =
      inner ℝ (b a) v := by
    simp [b, v, PiLp.inner_apply, Complex.mul_im, mul_comm]
  simp_rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two, hr, hi]
  rw [Finset.sum_add_distrib, b.sum_sq_inner_right, b.sum_sq_inner_right,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [u, v, Finset.sum_add_distrib]

lemma mass_pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : mass (ψ.pullback L) = mass ψ := by
  unfold mass H1Vector.pullback
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma kinetic_pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : kinetic (ψ.pullback L) = kinetic ψ := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun a _ =>
    ((ψ.pullback L).partial_L2 s a).integrable_norm_pow (p := 2) (by decide)),
    ← integral_finsetSum _ (fun a _ =>
      (ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide))]
  change (∫ x, ∑ a, ‖∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)‖^2) = _
  simp_rw [isometry_complex_gradient_sq]
  exact (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp' (fun x => ∑ a, ‖ψ.gradient s a x‖^2)

noncomputable section
lemma test_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hC.comp_left Complex.ofReal_zero)

lemma test_derivative_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) (a : Configuration n) :
    MemLp (fun x => (fderiv ℝ φ x a : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
    ((hC.fderiv_apply ℝ a).comp_left Complex.ofReal_zero)

def H1Vector.scale {n : ℕ} (c : ℂ) (u : H1Vector n) : H1Vector n where
  value := fun s x => c*u.value s x
  gradient := fun s a x => c*u.gradient s a x
  value_L2 := fun s => (u.value_L2 s).const_mul c
  partial_L2 := fun s a => (u.partial_L2 s a).const_mul c
  weak_partial := by
    intro s a φ hφ hC
    simp_rw [mul_assoc, integral_const_mul, u.weak_partial s a φ hφ hC]
    ring

def H1Vector.finiteSum {n : ℕ} {ι : Type*} [Fintype ι] (u : ι → H1Vector n) : H1Vector n where
  value := fun s x => ∑ i, (u i).value s x
  gradient := fun s a x => ∑ i, (u i).gradient s a x
  value_L2 := fun s => memLp_finsetSum _ (fun i _ => (u i).value_L2 s)
  partial_L2 := fun s a => memLp_finsetSum _ (fun i _ => (u i).partial_L2 s a)
  weak_partial := by
    intro s a φ hφ hC
    simp only [Finset.sum_mul]
    rw [integral_finsetSum (f := fun i x => (u i).value s x *
        (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) _ (fun i _ => (u i).value_L2 s |>.integrable_mul
      (test_derivative_L2 hφ hC (EuclideanSpace.single a 1))),
      integral_finsetSum (f := fun i x => (u i).gradient s a x * (φ x : ℂ))
        _ (fun i _ => (u i).partial_L2 s a |>.integrable_mul
      (test_L2 hφ hC))]
    simp_rw [H1Vector.weak_partial _ _ _ _ hφ hC]
    rw [Finset.sum_neg_distrib]

def permutationIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr p.symm (Equiv.refl _))

lemma permutationIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permutationIsometry p x = permute p x := by
  ext ⟨i,b⟩
  simp [permutationIsometry, permute, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permutationIsometry_single {n : ℕ} (p : Equiv.Perm (Fin n)) (a : Fin n × Fin 3) :
    permutationIsometry p (EuclideanSpace.single a 1) =
      EuclideanSpace.single (p.symm a.1,a.2) 1 := by
  rw [permutationIsometry_apply]
  ext ⟨i,b⟩
  simp [permute, PiLp.single_apply, Prod.ext_iff, ← Equiv.eq_symm_apply]

def H1Vector.permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) : H1Vector n where
  value := fun s => (u.pullback (permutationIsometry p)).value (s ∘ p)
  gradient := fun s => (u.pullback (permutationIsometry p)).gradient (s ∘ p)
  value_L2 := fun s => (u.pullback (permutationIsometry p)).value_L2 (s ∘ p)
  partial_L2 := fun s a => (u.pullback (permutationIsometry p)).partial_L2 (s ∘ p) a
  weak_partial := fun s a φ hφ hC =>
    (u.pullback (permutationIsometry p)).weak_partial (s ∘ p) a φ hφ hC

lemma permutation_value {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    (u.permutation p).value s x = u.value (s ∘ p) (permute p x) := by
  simp [H1Vector.permutation, H1Vector.pullback, permutationIsometry_apply]

lemma permutation_gradient {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (a : Fin n × Fin 3) (x : Configuration n) :
    (u.permutation p).gradient s a x =
      u.gradient (s ∘ p) (p.symm a.1,a.2) (permute p x) := by
  change (∑ k, ((permutationIsometry p (EuclideanSpace.single a 1)) k : ℂ) *
    u.gradient (s ∘ p) k (permutationIsometry p x)) = _
  rw [permutationIsometry_single, permutationIsometry_apply]
  simp [PiLp.single_apply, apply_ite]

lemma permute_one {n : ℕ} (x : Configuration n) : permute 1 x = x := by
  rfl
lemma permute_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) (x : Configuration n) :
    permute q (permute p x) = permute (p*q) x := by
  rfl
lemma permute_inv {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permute p⁻¹ (permute p x) = x := by
  rw [permute_mul, mul_inv_cancel, permute_one]
lemma permute_integral {n : ℕ} (p : Equiv.Perm (Fin n)) (F : Configuration n → ℂ) :
    (∫ x, F (permute p x)) = ∫ x, F x := by
  have H := (show MeasurePreserving (permutationIsometry p).toHomeomorph.toMeasurableEquiv
    volume volume from (permutationIsometry p).measurePreserving).integral_comp' F
  exact H

def permutationSpins {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n :=
  Equiv.arrowCongr p.symm (Equiv.refl _)
lemma permutationSpins_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (s : Spins n) :
    permutationSpins p s = s ∘ p := rfl

lemma sign_complex_sq {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((p.sign : ℤ) : ℂ)*((p.sign : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or p.sign with h|h <;> simp [h]

lemma sign_complex_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    (((p*q).sign : ℤ) : ℂ) = ((p.sign : ℤ) : ℂ)*((q.sign : ℤ) : ℂ) := by
  simp

def H1Vector.fullAntisymmetrize {n : ℕ} (u : H1Vector n) : H1Vector n :=
  H1Vector.finiteSum (fun p : Equiv.Perm (Fin n) =>
    (u.permutation p).scale (((p.sign : ℤ) : ℂ)))

lemma fullAntisymmetrize_value {n : ℕ} (u : H1Vector n) (s : Spins n) (x : Configuration n) :
    u.fullAntisymmetrize.value s x =
      ∑ p : Equiv.Perm (Fin n), ((p.sign : ℤ) : ℂ)*u.value (s ∘ p) (permute p x) := by
  simp [H1Vector.fullAntisymmetrize, H1Vector.finiteSum, H1Vector.scale, permutation_value]

lemma fullAntisymmetrize_antisymmetric {n : ℕ} (u : H1Vector n) :
    Antisymmetric u.fullAntisymmetrize := by
  intro p s
  filter_upwards [] with x
  rw [fullAntisymmetrize_value, fullAntisymmetrize_value, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft p⁻¹)
    (fun q => ((q.sign : ℤ) : ℂ)*u.value ((s ∘ p) ∘ q) (permute q (permute p x)))]
  apply Finset.sum_congr rfl
  intro q _
  change (((p⁻¹*q).sign : ℤ) : ℂ)*u.value ((s ∘ p) ∘ ((p⁻¹*q) : Equiv.Perm (Fin n)))
    (permute (p⁻¹*q) (permute p x)) = _
  rw [permute_mul, mul_inv_cancel_left]
  have hs : (s ∘ p) ∘ ((p⁻¹*q) : Equiv.Perm (Fin n)) = s ∘ q := by
    funext i
    simp
  rw [hs, sign_complex_mul]
  simp only [Equiv.Perm.sign_inv]
  ring
end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
