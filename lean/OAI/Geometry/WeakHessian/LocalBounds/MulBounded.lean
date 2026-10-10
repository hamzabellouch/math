import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AeAcRepresentativeMeasurable

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma LocallyL2.mul_bounded {f g : X → ℝ} (hf : LocallyL2 m f)
    (hg : AEStronglyMeasurable g m) {B : ℝ} (hb : ∀ᵐ x ∂m, |g x| ≤ B) :
    LocallyL2 m (fun x => f x * g x) := by
  intro o R hR
  apply ((hf o R hR).const_mul B).mono ((hf.aestronglyMeasurable.mul hg).restrict)
  filter_upwards [ae_restrict_of_ae hb] with x hx
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  calc
    |f x| * |g x| ≤ |f x| * |B| :=
      mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)
    _ = |B| * |f x| := mul_comm _ _

lemma IsLocalWeakUpperGradient.mul_bounded {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : LocallyL2 m f) (hg : AEMeasurable g m)
    {A B : ℝ} (hgB : ∀ᵐ x ∂m, |g x| ≤ A) (hEB : ∀ᵐ x ∂m, |E x| ≤ B) :
    IsLocalWeakUpperGradient m (fun x => f x * g x)
      (fun x => |g x| * D x + |f x| * E x) := by
  have hcalD : LocallyL2 m (fun x => |g x| * D x) := by
    simpa only [mul_comm] using hD.1.mul_bounded hg.abs.aestronglyMeasurable
      (by simpa only [abs_abs] using hgB)
  have hfn : LocallyL2 m (fun x => |f x|) := fun o R hR => by
    simpa only [Real.norm_eq_abs] using (hf o R hR).norm
  have hcalE : LocallyL2 m (fun x => |f x| * E x) :=
    hfn.mul_bounded hE.1.aestronglyMeasurable hEB
  refine ⟨fun o R hR => (hcalD o R hR).add (hcalE o R hR), ?_, ?_⟩
  · filter_upwards [hD.2.1,hE.2.1] with x hDx hEx
    exact add_nonneg (mul_nonneg (abs_nonneg _) hDx) (mul_nonneg (abs_nonneg _) hEx)
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf.aemeasurable hπ hb,
        hE.ae_exists_ac_representative hg hπ hb,
        hπ.ae_ae_eval_of_ae hD.2.1, hπ.ae_ae_eval_of_ae hE.2.1] with γ hq hr hDn hEn
    obtain ⟨q,hq,hq0,hq1,hqeq,hqd⟩ := hq
    obtain ⟨r,hr,hr0,hr1,hreq,hrd⟩ := hr
    have hp : AbsolutelyContinuousOnInterval (fun t => q t * r t) 0 1 := hq.mul hr
    have hder : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv (fun t => q t * r t) t| ≤
          ENNReal.ofReal (|g (evalReal γ t)| * D (evalReal γ t) +
            |f (evalReal γ t)| * E (evalReal γ t)) * metricSpeed γ t := by
      filter_upwards [hqeq,hreq,hqd,hrd,hDn,hEn,
        ae_restrict_of_ae hq.ae_differentiableAt, ae_restrict_of_ae hr.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t hqt hrt hd he hDn hEn hqa hra htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      change ENNReal.ofReal |deriv (q * r) t| ≤ _
      rw [deriv_mul (hqa htt) (hra htt)]
      calc
        ENNReal.ofReal |deriv q t * r t + q t * deriv r t| ≤
            ENNReal.ofReal (|r t| * |deriv q t| + |q t| * |deriv r t|) := by
          apply ENNReal.ofReal_le_ofReal
          simpa only [abs_mul, mul_comm (|deriv q t|)] using
            abs_add_le (deriv q t * r t) (q t * deriv r t)
        _ = ENNReal.ofReal |r t| * ENNReal.ofReal |deriv q t| +
            ENNReal.ofReal |q t| * ENNReal.ofReal |deriv r t| := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ ENNReal.ofReal |r t| * (ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t) +
            ENNReal.ofReal |q t| * (ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t) :=
          add_le_add (mul_le_mul' le_rfl hd) (mul_le_mul' le_rfl he)
        _ = _ := by
          rw [hqt,hrt, ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hDn)
            (mul_nonneg (abs_nonneg _) hEn), ENNReal.ofReal_mul (abs_nonneg _),
            ENNReal.ofReal_mul (abs_nonneg _), add_mul, mul_assoc, mul_assoc]
    calc
      ENNReal.ofReal |f (γ timeOne) * g (γ timeOne) - f (γ timeZero) * g (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv (fun t => q t * r t) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hp.integral_deriv_eq_sub,
          hq0,hq1,hr0,hr1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t => q t * r t) t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder)

end WeakHessian

namespace WeakHessian
lemma ac_comp_lipschitzOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ → X} {a b : ℝ} (hq : AbsolutelyContinuousOnInterval q a b)
    {φ : X → Y} {s : Set X} {L : ℝ≥0} (hφ : LipschitzOnWith L φ s)
    (hs : MapsTo q (uIcc a b) s) : AbsolutelyContinuousOnInterval (φ ∘ q) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hq ⊢
  intro ε hε
  obtain ⟨δ,hδ,hδq⟩ := hq (ε / (L + 1)) (by positivity)
  refine ⟨δ,hδ,?_⟩
  rintro ⟨n,I⟩ hI hlen
  have hsum := hδq (n,I) hI hlen
  calc
    ∑ i ∈ Finset.range n, dist ((φ ∘ q) (I i).1) ((φ ∘ q) (I i).2) ≤
        L * ∑ i ∈ Finset.range n, dist (q (I i).1) (q (I i).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact hφ.dist_le_mul _ (hs (hI.1 i hi).1) _ (hs (hI.1 i hi).2)
    _ ≤ L * (ε / (L + 1)) := by gcongr
    _ < (L + 1) * (ε / (L + 1)) := by gcongr; linarith
    _ = ε := by field

lemma ac_comp_contDiff {q : ℝ → ℝ} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    AbsolutelyContinuousOnInterval (φ ∘ q) a b := by
  obtain ⟨M,hM⟩ := hq.exists_bound
  obtain ⟨L,hL⟩ := (hφ.contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn hq hL
  intro t ht
  simpa only [Real.norm_eq_abs, mem_Icc, abs_le] using hM t ht

end WeakHessian

end
end InlinedFile0

end OAI
