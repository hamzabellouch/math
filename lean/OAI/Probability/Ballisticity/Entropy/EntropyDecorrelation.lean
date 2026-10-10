import Mathlib
import OAI.Probability.Ballisticity.Walk.Rows
import OAI.Probability.Ballisticity.Entropy.EntropyPlus

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

section Unbounded

variable {D I A : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

lemma entropy_decorrelation {f : D × (I → A) → ℝ} {Z : ℕ → D × (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x)
      ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ Q)
    (hZsi : ∀ r d, Integrable (fun ω => Z r (d, ω)) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ r d, (∫ ω, Z r (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hloc : ∀ K > 0, EscapingLocalApproximation δ ν (fun r x => min K (Z r x)) K) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x, f x * Z r x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let μ := δ.prod P
  have hprod (r : ℕ) : Integrable (fun x => f x * Z r x) μ := by
    apply integrable_density_mul_of_entropy (c := 2 * c) (by positivity) hf (hZ r) hf0 (hZ0 r) hH (he r)
  intro ε hε
  have ht : 0 < ε / 3 := by positivity
  obtain ⟨B, hB, htail⟩ := uniform_density_tail hc hf hf0 hfi hH hZ hZ0 he heQ (ε / 3) ht
  let b : D × (I → A) → ℝ := fun x => min B (f x)
  have hb : Measurable b := measurable_const.min hf
  have hb0 : ∀ x, 0 ≤ b x := fun x => le_min (by linarith) (hf0 x)
  have hbB : ∀ x, b x ≤ B := fun x => min_le_left _ _
  have hbf : ∀ x, b x ≤ f x := fun x => min_le_right _ _
  have hbi : Integrable b μ := integrable_bounded_nonneg hb hb0 hbB
  have hbm : (∫ x, b x ∂μ) ≤ 1 := by
    rw [← hf1]
    exact integral_mono hbi hfi hbf
  obtain ⟨K, hK, hcap⟩ := uniform_remainder_cap hc (by linarith : 0 ≤ B)
    hb hb0 hbB hZ hZ0 he heQ (ε / 3) ht
  let ZK : ℕ → D × (I → A) → ℝ := fun r x => min K (Z r x)
  have hZK (r : ℕ) : Measurable (ZK r) := measurable_const.min (hZ r)
  have hZK0 (r : ℕ) (x : D × (I → A)) : 0 ≤ ZK r x := le_min hK.le (hZ0 r x)
  have hZKB (r : ℕ) (x : D × (I → A)) : ZK r x ≤ K := min_le_left _ _
  have hZKC (r : ℕ) (d : D) : (∫ ω, ZK r (d, ω) ∂P) ≤ C := by
    apply le_trans _ (hZC r d)
    exact integral_mono
      (integrable_bounded_nonneg ((hZK r).comp (measurable_const.prodMk measurable_id))
        (fun ω => hZK0 r (d, ω)) (fun ω => hZKB r (d, ω)))
      (hZsi r d) (fun _ => min_le_right _ _)
  have hbd := bounded_decorrelation δ ν (by linarith : 0 ≤ B) hK.le hC hb hb0 hbB
    hZK hZK0 hZKB hZKC (hloc K hK) (ε / 3) ht
  filter_upwards [hbd] with r hr
  have hcapi : Integrable (fun x => b x * (Z r x - min K (Z r x))) μ :=
    cap_error_integrable (K := K) hc (by linarith) hb (hZ r) hb0 hbB (hZ0 r) (he r)
  have htaili : Integrable (fun x => if B < f x then f x * Z r x else 0) μ := by
    apply (hprod r).norm.mono'
      ((hf.mul (hZ r)).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖if B < f x then f x * Z r x else 0‖ ≤ ‖f x * Z r x‖
    split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]
  have hbZi : Integrable (fun x => b x * ZK r x) μ :=
    integrable_bounded_nonneg (hb.mul (hZK r))
      (fun x => mul_nonneg (hb0 x) (hZK0 r x))
      (fun x => mul_le_mul (hbB x) (hZKB r x) (hZK0 r x) (by linarith))
  have hsum : Integrable (fun x => b x * ZK r x +
      (if B < f x then f x * Z r x else 0)) μ := hbZi.add htaili
  have hi := integral_mono (hprod r) (hsum.add hcapi) (fun x => show f x * Z r x ≤
      (b x * ZK r x + (if B < f x then f x * Z r x else 0)) +
        b x * (Z r x - min K (Z r x)) by
    by_cases hx : B < f x
    · rw [ite_eq_left hx]
      dsimp [ZK]
      nlinarith [mul_nonneg (hb0 x) (hZ0 r x)]
    · rw [ite_eq_right hx]
      have heq : b x = f x := min_eq_right (le_of_not_gt hx)
      rw [heq]
      dsimp [ZK]
      ring_nf
      exact le_rfl)
  change (∫ x, f x * Z r x ∂μ) ≤ ∫ x,
      (b x * ZK r x + (if B < f x then f x * Z r x else 0)) +
        b x * (Z r x - min K (Z r x)) ∂μ at hi
  rw [integral_add hsum hcapi, integral_add hbZi htaili] at hi
  have h1 : C * (∫ x, b x ∂μ) ≤ C := by nlinarith [hbm]
  have h2 := htail r
  have h3 := hcap r
  change (∫ x, b x * ZK r x ∂μ) ≤ C * (∫ x, b x ∂μ) + ε / 3 at hr
  change (∫ x, f x * Z r x ∂μ) ≤ C + ε
  nlinarith

end Unbounded

end TailDecorrelation

end

end OAI
