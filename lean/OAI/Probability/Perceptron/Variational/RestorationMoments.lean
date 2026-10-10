import Mathlib
import OAI.Probability.Perceptron.Interpolation.IntegrableReplicaGibbs
import OAI.Probability.Perceptron.Cascade.ReweightedMomentLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

def restorationReplicaTest (r : ℕ) (W : S→ℝ) (F : (Fin r→S)→ℝ) :
    (k : ℕ) → (Fin (r+k)→S)→ℝ
  | 0 => F
  | k+1 => fun x => W (x 0)*restorationReplicaTest r W F k (fun i => x i.succ)

lemma restorationReplicaTest_measurable (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    (hW : Measurable W) (hF : Measurable F) (k : ℕ) :
    Measurable (restorationReplicaTest r W F k) := by
  induction k with
  | zero => exact hF
  | succ k hk =>
    exact (hW.comp (measurable_pi_apply 0)).mul
      (hk.comp (Measurable.of_eval fun index => measurable_pi_apply index.succ))

omit [MeasurableSpace S] in
lemma restorationReplicaTest_bound (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    {D B : ℝ} (hD : 0≤D) (_hB : 0≤B) (hW : ∀ x, |W x|≤D) (hF : ∀ x, |F x|≤B)
    (k : ℕ) (x : Fin (r+k)→S) : |restorationReplicaTest r W F k x| ≤ D^k*B := by
  induction k with
  | zero => simpa only [restorationReplicaTest,pow_zero,one_mul] using hF x
  | succ k hk =>
    rw [restorationReplicaTest,abs_mul]
    exact (mul_le_mul (hW _) (hk _) (abs_nonneg _) hD).trans_eq (by ring)

lemma restoration_replica_moment (μ : Measure S) [IsProbabilityMeasure μ]
    {H W : S→ℝ} {r : ℕ} {F : (Fin r→S)→ℝ}
    (hH : Measurable H) (hW : Measurable W) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ)
    {D B : ℝ} (hD : 0≤D) (hB : 0≤B) (hWD : ∀ x, |W x|≤D) (hFB : ∀ x, |F x|≤B)
    (k : ℕ) :
    gibbsReplicaMean μ H (r+k) (restorationReplicaTest r W F k) =
      (tiltMean μ H W 1)^k*gibbsReplicaMean μ H r F := by
  induction k with
  | zero => simp only [restorationReplicaTest,pow_zero,one_mul,Nat.add_zero]
  | succ k hk =>
    change gibbsReplicaMean μ H ((r+k)+1) (fun x => W (x 0)*restorationReplicaTest r W F k (fun i => x i.succ)) = _
    rw [gibbsReplicaMean_product_of_integrable μ hH hW
        (restorationReplicaTest_measurable r hW hF k) hi hWD
        (restorationReplicaTest_bound r hD hB hWD hFB k), hk]
    ring

lemma restoration_ratio_tendsto {Ω : ℕ→Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    (μ : (n : ℕ)→Measure (Ω n)) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {a b : ℝ} (ha : 0<a)
    (A : (n : ℕ)→Ω n→ℝ) (A' : Ω'→ℝ)
    (Z : (n : ℕ)→Ω n→Icc a b) (Z' : Ω'→Icc a b)
    (hA : ∀ n, Measurable (A n)) (hA' : Measurable A')
    (hZ : ∀ n, Measurable (Z n)) (hZ' : Measurable Z')
    {C : ℝ} (hC : 0≤C) (hb : ∀ n x, |A n x|≤C) (hb' : ∀ x, |A' x|≤C)
    (hm : ∀ k : ℕ, Tendsto (fun n => ∫ x, A n x*(Z n x).val^k ∂μ n) atTop
      (𝓝 (∫ x, A' x*(Z' x).val^k ∂ν))) (r : ℕ) :
    Tendsto (fun n => ∫ x, A n x/(Z n x).val^r ∂μ n) atTop
      (𝓝 (∫ x, A' x/(Z' x).val^r ∂ν)) := by
  let F : C(Icc a b,ℝ) := ⟨fun z => (z.val^r)⁻¹,
    (continuous_subtype_val.pow r).inv₀ fun x => pow_ne_zero _ (ne_of_gt (ha.trans_le x.prop.1))⟩
  simpa only [F, ContinuousMap.coe_mk, div_eq_mul_inv] using bounded_weighted_moment_limit μ ν A A' Z Z' hA hA' hZ hZ'
    C hC hb hb' hm F

end SphericalPerceptronFreeEnergy
end

end OAI
