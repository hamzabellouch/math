import OAI.Combinatorics.BalancedRyser.Local.MeasureLocalLemma
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

theorem local_lemma_of_half_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxhalf : ∀ i, x i ≤ 1 / 2)
    (hp : ∀ i, μ.real (B i) ≤ x i / 2)
    (hweight : ∀ i, ∑ j ∈ N i, x j ≤ 1 / 2)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T)) :
    ∀ S, 0 < μ.real (avoid B S) ∧ ∀ i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S) := by
  apply local_lemma μ B hB N x hx0 (fun i => by linarith [hxhalf i]) _ hind
  intro i
  have hprod := Balanced.one_sub_sum_le_avoidance_prod (N i) x
    (fun j _ => hx0 j) (fun j _ => by linarith [hxhalf j])
  have hlower : (1 / 2 : ℝ) ≤ ∏ j ∈ N i, (1 - x j) := by
    linarith [hweight i]
  have hm := mul_le_mul_of_nonneg_left hlower (hx0 i)
  linarith [hp i]

theorem local_lemma_cylinder_exp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxhalf : ∀ i, x i ≤ 1 / 2)
    (hp : ∀ i, μ.real (B i) ≤ x i / 2)
    (hweight : ∀ i, ∑ j ∈ N i, x j ≤ 1 / 2)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T))
    (C : Set Ω) (T U : Finset ι) (hdisj : Disjoint T U)
    (hC : μ.real (C ∩ avoid B T) = μ.real C * μ.real (avoid B T))
    (s : ℝ) (hs : ∑ i ∈ U, x i ≤ s / 4) :
    0 < μ.real (avoid B (T ∪ U)) ∧
      μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
        Real.exp (s / 2) * μ.real C := by
  have h := local_lemma_of_half_weight μ B hB N x hx0 hxhalf hp hweight hind
  refine ⟨(h _).1, ?_⟩
  have hc := conditional_event_bound μ B x hB (fun i => by linarith [hxhalf i])
    (fun S i hi => (h S).2 i hi) C T U hdisj (h _).1 hC
  have he := Balanced.prod_inv_one_sub_le_exp_half U x s
    (fun i _ => hx0 i) (fun i _ => hxhalf i) hs
  calc
    μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
        μ.real C * ∏ i ∈ U, (1 - x i)⁻¹ := hc
    _ ≤ μ.real C * Real.exp (s / 2) :=
      mul_le_mul_of_nonneg_left he measureReal_nonneg
    _ = Real.exp (s / 2) * μ.real C := mul_comm _ _

end Balanced.CylinderConditioning

end OAI
