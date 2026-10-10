import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkFreshRestore
import OAI.Probability.Perceptron.Interpolation.GaussianReplicaFubini
import OAI.Probability.Perceptron.Interpolation.RestorationReplicaBlocks

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev TwoFreshDisorder (N M : ℕ) := BulkDisorder N M ×
  (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))

def bulkMarkedTest (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))
    (x : Fin r → NormalizedSpin N) : ℝ :=
  F (fun i j => bulkOverlap (x i) (x j))*
    Ψ (gaussianRows (fun i => (x i).val) z.1)*Φ (gaussianRows (fun i => (x i).val) z.2)

lemma bulkMarkedTest_continuous (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Continuous (Function.uncurry (bulkMarkedTest N r F Ψ Φ)) := by
  have hF : Continuous (fun x : Fin r → NormalizedSpin N => F (fun i j => bulkOverlap (x i) (x j))) := by
    apply F.continuous.comp
    unfold bulkOverlap spinOverlap
    fun_prop
  have hv : Continuous (fun x : NormalizedSpin N => x.val) := continuous_subtype_val
  have hg : Continuous (fun p : EuclideanSpace ℝ (Fin N) × (Fin r → NormalizedSpin N) =>
      gaussianRows (fun i => (p.2 i).val) p.1) :=
    gaussianRows_joint_continuous hv
  have hp₁ : Continuous (fun p : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) ×
      (Fin r → NormalizedSpin N) => (p.1.1,p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hp₂ : Continuous (fun p : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) ×
      (Fin r → NormalizedSpin N) => (p.1.2,p.2)) :=
    continuous_fst.snd.prodMk continuous_snd
  have h₁ := Ψ.continuous.comp (hg.comp hp₁)
  have h₂ := Φ.continuous.comp (hg.comp hp₂)
  exact ((hF.comp continuous_snd).mul h₁).mul h₂

lemma bulkMarkedTest_bound (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) (x : Fin r → NormalizedSpin N) :
    |bulkMarkedTest N r F Ψ Φ z x| ≤ ‖F‖*‖Ψ‖*‖Φ‖ := by
  unfold bulkMarkedTest
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (F.norm_coe_le_norm _) (Ψ.norm_coe_le_norm _)
    (abs_nonneg _) (norm_nonneg _)) (Φ.norm_coe_le_norm _) (abs_nonneg _) (by positivity)

def bulkFreshNumerator (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (p : TwoFreshDisorder (n+1) M) : ℝ :=
  gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2) r
    (bulkMarkedTest (n+1) r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) p.2)

def bulkFreshDenominator (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (p : TwoFreshDisorder (n+1) M) : ℝ :=
  tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1

lemma twoFreshHamiltonian_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f v p.1.1.1 p.1.1.2 p.2) := by
  have hp : Continuous (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
      (p.1.1,p.2)) := continuous_fst.fst.prodMk continuous_snd
  exact ((bulkHamiltonian_continuous (n+1) M f v).comp hp).measurable

lemma twoFreshMarkedTest_measurable (n M r : ℕ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Measurable (fun p : TwoFreshDisorder (n+1) M × (Fin r → NormalizedSpin (n+1)) =>
      bulkMarkedTest (n+1) r F Ψ Φ p.1.2 p.2) := by
  have hp : Continuous (fun p : TwoFreshDisorder (n+1) M × (Fin r → NormalizedSpin (n+1)) =>
      (p.1.2,p.2)) := continuous_fst.snd.prodMk continuous_snd
  exact ((bulkMarkedTest_continuous (n+1) r F Ψ Φ).comp hp).measurable

lemma bulkFreshNumerator_measurable (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Measurable (bulkFreshNumerator n M r f v F Ψ Φ) := by
  let H := fun (p : TwoFreshDisorder (n+1) M) (x : NormalizedSpin (n+1)) =>
    bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x
  let G := fun (p : TwoFreshDisorder (n+1) M) (x : Fin r → NormalizedSpin (n+1)) =>
    bulkMarkedTest (n+1) r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) p.2 x
  change Measurable (fun p => gibbsReplicaMean (unitSphereLaw (n+1)) (H p) r (G p))
  exact kernel_replicaMean_measurable (Kernel.const (TwoFreshDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=H) (G:=G) (twoFreshHamiltonian_measurable n M f v)
    (twoFreshMarkedTest_measurable n M r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0))

lemma bulkFreshDenominator_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (bulkFreshDenominator n M f v) := by
  apply kernel_tiltMean_measurable (Kernel.const (TwoFreshDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=fun p x => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x)
    (twoFreshHamiltonian_measurable n M f v)
  change Measurable (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
    Real.exp (f (inner ℝ p.2.val p.1.2.1)+f (inner ℝ p.2.val p.1.2.2)))
  exact (((f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd.fst)).add
    (f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd.snd))).exp)

lemma bulkFreshNumerator_bound (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (p : TwoFreshDisorder (n+1) M) :
    |bulkFreshNumerator n M r f v F Ψ Φ p| ≤
      ‖F‖*‖restorationMarkTest r f Ψ 0‖*‖restorationMarkTest r f Φ 0‖ := by
  apply gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    ((bulkMarkedTest_continuous (n+1) r F (restorationMarkTest r f Ψ 0)
      (restorationMarkTest r f Φ 0)).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v p.1)
  exact bulkMarkedTest_bound _ _ _ _ _ _

lemma bulkFreshDenominator_mem (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) (p : TwoFreshDisorder (n+1) M) :
    bulkFreshDenominator n M f v p ∈ Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) := by
  change Real.exp (-(2*‖f‖)) ≤ tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1 ∧
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1 ≤ Real.exp (2*‖f‖)
  exact bulk_two_denominator_bounds n M f v p.1 p.2.1 p.2.2

lemma bulkMarked_replica_moment (N r : ℕ) (μ : Measure (NormalizedSpin N)) [IsProbabilityMeasure μ]
    {H : NormalizedSpin N → ℝ} (hH : Measurable H) (he : Integrable (fun x => Real.exp (H x)) μ)
    (f : ℝ →ᵇ ℝ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :
    (tiltMean μ H (fun x => Real.exp (f (inner ℝ x.val z.1)+f (inner ℝ x.val z.2))) 1)^k *
      gibbsReplicaMean μ H r (bulkMarkedTest N r F (restorationMarkTest r f Ψ 0)
        (restorationMarkTest r f Φ 0) z) =
      gibbsReplicaMean μ H (r+k) (bulkMarkedTest N (r+k) (restorationBlockTest r F k)
        (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k) z) := by
  let W := fun x : NormalizedSpin N => Real.exp (f (inner ℝ x.val z.1)+f (inner ℝ x.val z.2))
  let A := bulkMarkedTest N r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) z
  have hW : Measurable W := ((f.measurable.comp (measurable_subtype_coe.inner measurable_const)).add
    (f.measurable.comp (measurable_subtype_coe.inner measurable_const))).exp
  have hpA : Continuous (fun x : Fin r → NormalizedSpin N => (z,x)) :=
    continuous_const.prodMk continuous_id
  have hA : Measurable A := ((bulkMarkedTest_continuous N r F (restorationMarkTest r f Ψ 0)
    (restorationMarkTest r f Φ 0)).comp hpA).measurable
  have hWb (x) : |W x|≤Real.exp (2*‖f‖) := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (le_abs_self (f (inner ℝ x.val z.1))).trans (f.norm_coe_le_norm _)
    have := (le_abs_self (f (inner ℝ x.val z.2))).trans (f.norm_coe_le_norm _)
    linarith
  have h := restoration_replica_moment μ hH hW hA he (Real.exp_pos _).le (by positivity)
    hWb (bulkMarkedTest_bound N r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) z) k
  change _ = _ at h
  rw [←h]
  congr 1
  funext x
  have h₀ := funext (restorationReplicaTest_twoMarks f F Ψ Φ z.1 z.2 0)
  change _ = A at h₀
  rw [←h₀]
  exact restorationReplicaTest_twoMarks f F Ψ Φ z.1 z.2 k x

lemma bulkFresh_polynomial_moment (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) (p : TwoFreshDisorder (n+1) M) :
    bulkFreshDenominator n M f v p^k*bulkFreshNumerator n M r f v F Ψ Φ p =
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
        (r+k) (bulkMarkedTest (n+1) (r+k) (restorationBlockTest r F k)
          (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k) p.2) := by
  exact bulkMarked_replica_moment (n+1) r (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v p.1) f F Ψ Φ k p.2

end SphericalPerceptronFreeEnergy
end

end OAI
