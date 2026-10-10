import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectation

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
noncomputable def stationaryInner {n : ℕ} (J : Interaction n) (f g : Observables n) : ℝ :=
  gibbsExpectation J (fun x => f x * g x)
noncomputable def weightedInner {n : ℕ} (J : Interaction n) (p q : VectorFields n) : ℝ :=
  gibbsExpectation J (fun x => ∑ i, siteVariance J x i * p x i * q x i)
noncomputable def equilibriumPotential {n : ℕ} (J : Interaction n) (δ : ℝ)
    (B : VectorFields n) (x : Spin n) : ℝ :=
  δ⁻¹ * ((∑ i, spin x i * semigroup J δ (fun y => B y i) x) -
    semigroup J δ (fun y => ∑ i, semigroup J δ (fun z => spin z i) y * B y i) x)

noncomputable def expectationLM {n : ℕ} (J : Interaction n) : Observables n →ₗ[ℝ] ℝ where
  toFun := gibbsExpectation J
  map_add' f g := by simp [gibbsExpectation, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [gibbsExpectation, mul_left_comm, ← Finset.mul_sum]

noncomputable def expectationCLM {n : ℕ} (J : Interaction n) : Observables n →L[ℝ] ℝ :=
  (expectationLM J).toContinuousLinearMap

lemma gibbsExpectation_const {n : ℕ} (J : Interaction n) (c : ℝ) :
    gibbsExpectation J (fun _ => c) = c := by
  simp only [gibbsExpectation, ← Finset.sum_mul, gibbs_sum, one_mul]

lemma gibbsExpectation_sum {n : ℕ} {α : Type*} [Fintype α] (J : Interaction n)
    (f : α → Observables n) :
    gibbsExpectation J (fun x => ∑ a, f a x) = ∑ a, gibbsExpectation J (f a) := by
  simp only [gibbsExpectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma gibbsExpectation_sub {n : ℕ} (J : Interaction n) (f g : Observables n) :
    gibbsExpectation J (fun x => f x - g x) = gibbsExpectation J f - gibbsExpectation J g := by
  simp only [gibbsExpectation, mul_sub, Finset.sum_sub_distrib]

lemma gibbsExpectation_mul_const {n : ℕ} (J : Interaction n) (c : ℝ) (f : Observables n) :
    gibbsExpectation J (fun x => c * f x) = c * gibbsExpectation J f := by
  simp only [gibbsExpectation, mul_left_comm (gibbs J _) c, ← Finset.mul_sum]

noncomputable def stationaryPairingCLM {n : ℕ} (J : Interaction n) (f : Observables n) :
    Observables n →L[ℝ] ℝ :=
  (show Observables n →ₗ[ℝ] ℝ from
    { toFun := stationaryInner J f
      map_add' g h := by simp [stationaryInner, gibbsExpectation, mul_add, Finset.sum_add_distrib]
      map_smul' c g := by simp [stationaryInner, gibbsExpectation, mul_left_comm, ← Finset.mul_sum]
    }).toContinuousLinearMap

@[simp] lemma expectationCLM_apply {n : ℕ} (J : Interaction n) (f : Observables n) :
    expectationCLM J f = gibbsExpectation J f := rfl

@[simp] lemma stationaryPairingCLM_apply {n : ℕ} (J : Interaction n) (f g : Observables n) :
    stationaryPairingCLM J f g = stationaryInner J f g := rfl

lemma stationaryInner_symm {n : ℕ} (J : Interaction n) (f g : Observables n) :
    stationaryInner J f g = stationaryInner J g f := by
  simp only [stationaryInner, mul_comm (f _) (g _)]

lemma dirichlet_symm {n : ℕ} (J : Interaction n) (f g : Observables n) :
    dirichlet J f g = dirichlet J g f := by
  unfold dirichlet
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma scalar_generator_symmetric {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f g : Observables n) :
    stationaryInner J f (generator J g) = stationaryInner J (generator J f) g := by
  have hf := gibbs_dirichlet J hJ hdiag f g
  have hg := gibbs_dirichlet J hJ hdiag g f
  rw [dirichlet_symm J g f, ← hf] at hg
  simp only [gibbsExpectation, mul_neg, Finset.sum_neg_distrib] at hg
  unfold stationaryInner gibbsExpectation
  simpa only [mul_comm (g _) (generator J f _)] using (neg_inj.mp hg).symm

lemma stationaryInner_pow_symm {n : ℕ} (J : Interaction n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f g, stationaryInner J f (A g) = stationaryInner J (A f) g)
    (k : ℕ) (f g : Observables n) :
    stationaryInner J f ((A ^ k) g) = stationaryInner J ((A ^ k) f) g := by
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
    calc
      _ = stationaryInner J (A f) ((A ^ k) g) := by
        rw [pow_succ', mul_apply_eq_comp, hA]
      _ = stationaryInner J ((A ^ k) (A f)) g := ih (A f) g
      _ = _ := by rw [pow_succ, mul_apply_eq_comp]

lemma stationaryInner_exp_symm {n : ℕ} (J : Interaction n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f g, stationaryInner J f (A g) = stationaryInner J (A f) g)
    (f g : Observables n) :
    stationaryInner J f (NormedSpace.exp A g) = stationaryInner J (NormedSpace.exp A f) g := by
  have hf : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * stationaryInner J f ((A ^ k) g))
      (stationaryInner J f (NormedSpace.exp A g)) := by
    simpa only [map_smul, smul_eq_mul, stationaryPairingCLM_apply] using (stationaryPairingCLM J f).hasSum (exp_apply_hasSum A g)
  have hg : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * stationaryInner J g ((A ^ k) f))
      (stationaryInner J g (NormedSpace.exp A f)) := by
    simpa only [map_smul, smul_eq_mul, stationaryPairingCLM_apply] using (stationaryPairingCLM J g).hasSum (exp_apply_hasSum A f)
  have hp (k : ℕ) : stationaryInner J f ((A ^ k) g) = stationaryInner J g ((A ^ k) f) := by
    rw [stationaryInner_pow_symm J A hA, stationaryInner_symm]
  simp_rw [hp] at hf
  rw [← stationaryInner_symm J g]
  exact hf.unique hg

theorem scalar_semigroup_symmetric {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f g : Observables n) :
    stationaryInner J f (semigroup J t g) = stationaryInner J (semigroup J t f) g := by
  apply stationaryInner_exp_symm
  intro a b
  change gibbsExpectation J (fun x => a x * (t * generator J b x)) =
    gibbsExpectation J (fun x => (t * generator J a x) * b x)
  simp only [mul_assoc, mul_left_comm (a _) t, gibbsExpectation_mul_const]
  exact congrArg (fun r : ℝ => t * r) (scalar_generator_symmetric J hJ hdiag a b)

lemma gibbsExpectation_semigroup {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f : Observables n) : gibbsExpectation J (semigroup J t f) = gibbsExpectation J f := by
  have h (g : Observables n) : expectationCLM J ((t • generatorCLM J) g) =
      (0 : ℝ →L[ℝ] ℝ) (expectationCLM J g) := by
    rw [smul_apply, map_smul]
    change t * gibbsExpectation J (generator J g) = 0
    rw [gibbs_generator_zero J hJ hdiag, mul_zero]
  simpa only [NormedSpace.exp_zero, one_apply_eq_self, expectationCLM_apply, semigroup] using
    exp_intertwine (t • generatorCLM J) (0 : ℝ →L[ℝ] ℝ) (expectationCLM J) h f

theorem equilibriumPotential_centered {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (δ : ℝ) (B : VectorFields n) : gibbsExpectation J (equilibriumPotential J δ B) = 0 := by
  unfold equilibriumPotential
  rw [gibbsExpectation_mul_const, gibbsExpectation_sub,
    gibbsExpectation_semigroup J hJ hdiag, gibbsExpectation_sum, gibbsExpectation_sum]
  have he (i : Fin n) := scalar_semigroup_symmetric J hJ hdiag δ
    (fun x => spin x i) (fun x => B x i)
  simp only [stationaryInner] at he
  simp_rw [he]
  simp

lemma exact_gradient_semigroup_identity {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f g : Observables n) :
    weightedInner J (fun x i => halfDiff i f x)
      (gradientSemigroup J t (fun x i => halfDiff i g x)) =
      stationaryInner J f (fun x => -generator J (semigroup J t g) x) := by
  simp_rw [weightedInner, ← halfDiff_semigroup]
  exact (gibbs_dirichlet J hJ hdiag f (semigroup J t g)).symm

end SKGapCutoff

end

end OAI
