import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.FiniteDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

section TestTransfer
variable {X : Type*} [mX : MeasurableSpace X]

lemma original_le_completion (ν : Measure X) :
    mX ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace X ν)) :=
  fun _ hs => hs.nullMeasurableSet

lemma trim_completion (ν : Measure X) :
    ν.completion.trim (original_le_completion ν) = ν := by
  unfold NullMeasurableSpace at *
  apply Measure.ext
  intro S hS
  exact trim_measurableSet_eq (original_le_completion ν) hS

lemma lintegral_completion (ν : Measure X) {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν.completion) = ∫⁻ x, f x ∂ν := by
  have ht : @Measure.trim X mX (inferInstance : MeasurableSpace (NullMeasurableSpace X ν))
      ν.completion (original_le_completion ν) = ν := trim_completion ν
  have h := lintegral_trim_ae (α := X) (μ := ν.completion) (original_le_completion ν)
    (f := f) (by rwa [ht])
  rw [ht] at h
  exact h.symm

lemma eLpNorm_completion (ν : Measure X) (F : X → ℝ) (hF : Measurable F) (p : ℕ)
    (hp : p ≠ 0) : eLpNorm F (p:ℝ≥0∞) ν.completion = eLpNorm F (p:ℝ≥0∞) ν := by
  have hFc : @Measurable (NullMeasurableSpace X ν) ℝ _ _ F :=
    hF.mono (original_le_completion ν) le_rfl
  erw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness)
      hFc.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness)
      hF.aestronglyMeasurable,
    lintegral_completion ν (by fun_prop)]

lemma density_test_bound (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (p : ℕ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hnorm : eLpNorm F (p:ℝ≥0∞) ν ≤ B) (S : Set X) (hS : MeasurableSet S)
    (hsupp : ∀ᵐ x ∂ν, x ∉ S → F x = 0)
    (φ : X → ℝ≥0∞) (hφ : AEMeasurable φ ν) (hφ1 : ∀ x, φ x ≤ 1) :
    (∫⁻ x, φ x ∂ν.withDensity (fun x => ENNReal.ofReal (F x))) ≤
      B * (∫⁻ x in S, φ x ∂ν)^(1-1/(p:ℝ)) := by
  have hp' : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpq := Real.HolderConjugate.conjExponent hp'
  have hq : 1 / Real.conjExponent (p:ℝ) = 1-1/(p:ℝ) := by
    simpa only [one_div] using (eq_sub_of_add_eq' hpq.inv_add_inv_eq_one)
  let K := S.indicator φ
  have hK : AEMeasurable K ν := hφ.indicator hS
  have hK1 : ∀ x, K x ≤ 1 := by
    intro x
    exact (Set.indicator_le (g := fun _ => 1) (fun _ _ => hφ1 _)) x
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hF.ennreal_ofReal.aemeasurable) hφ]
  have he : (fun x => ENNReal.ofReal (F x) * φ x) =ᵐ[ν]
      (fun x => ENNReal.ofReal (F x) * K x) := by
    filter_upwards [hsupp] with x hx
    by_cases hxS : x ∈ S
    · simp [K, Set.indicator_of_mem hxS]
    · simp [K, Set.indicator_of_notMem hxS, hx hxS]
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hF.ennreal_ofReal.aemeasurable hK
  have hnormeq : (∫⁻ x, ENNReal.ofReal (F x) ^ (p:ℝ) ∂ν) ^ (1/(p:ℝ)) =
      eLpNorm F (p:ℝ≥0∞) ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p ≠ 0))
      (by finiteness) hF.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.enorm_eq_ofReal (hF0 _)]
  rw [hnormeq, hq] at hholder
  refine hholder.trans (mul_le_mul' hnorm ?_)
  apply ENNReal.rpow_le_rpow _ (by rw [← hq]; exact hpq.symm.one_div_nonneg)
  calc
    (∫⁻ x, K x ^ Real.conjExponent (p:ℝ) ∂ν) ≤ ∫⁻ x, K x ∂ν :=
      lintegral_mono (fun x => ENNReal.rpow_le_self_of_le_one (hK1 x) hpq.symm.lt.le)
    _ = _ := lintegral_indicator hS _

lemma density_set_bound (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (p : ℕ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hnorm : eLpNorm F (p:ℝ≥0∞) ν ≤ B) (E : Set X) (hE : MeasurableSet E) :
    ν.withDensity (fun x => ENNReal.ofReal (F x)) E ≤ B * (ν E)^(1-1/(p:ℝ)) := by
  have h := density_test_bound ν F hF hF0 p hp B hnorm Set.univ MeasurableSet.univ
    (by simp) (E.indicator 1) (measurable_one.indicator hE).aemeasurable
    (fun x => (Set.indicator_le (g := fun _ => (1:ℝ≥0∞)) (fun _ _ => le_rfl)) x)
  simpa only [lintegral_indicator hE, Measure.restrict_apply_univ,
    setLIntegral_const, Pi.one_apply, one_mul, Measure.restrict_univ] using h

lemma withDensity_completion_apply (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (E : Set X) (hE : NullMeasurableSet E ν) :
    ν.completion.withDensity (fun x => ENNReal.ofReal (F x)) E =
      ν.withDensity (fun x => ENNReal.ofReal (F x)) E := by
  erw [withDensity_apply _ hE, withDensity_apply₀ _ hE,
    ← lintegral_indicator hE, ← lintegral_indicator₀ hE,
    lintegral_completion ν (hF.ennreal_ofReal.aemeasurable.indicator₀ hE)]
end TestTransfer

def MeasurableTestStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    let ν := MatrixLabelReference d m
    let η := ProjectionLaw μ m
    let B := ENNReal.ofReal (ProjectionNormScale m p H β R)
    let α := 1-1/(p:ℝ)
    (∀ E, MeasurableSet E → ν E ≠ ∞ → η E ≤ B * (ν E)^α) ∧
    η ≪ ν ∧
    ∃ ηc : Measure (NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν),
      (∀ E, NullMeasurableSet E ν → ηc E = η E) ∧
      (∀ E, NullMeasurableSet E ν → ν.completion E ≠ ∞ →
        ηc E ≤ B * (ν.completion E)^α) ∧
      (∀ φ : NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν → ℝ≥0∞,
        Measurable φ → (∀ x, φ x ≤ 1) →
        (∫⁻ x, φ x ∂ηc) ≤ B * (∫⁻ x in ProjectedEllipsoid z R, φ x ∂ν.completion)^α)
theorem measurable_test : MeasurableTestStatement := by
  intro d m p hd hm hp β H R hgap hH hR z μ hμ hs hb
  let := hμ
  obtain ⟨F, hF, hF0, hden, hsupp, hnorm⟩ :=
    exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
  dsimp only
  let ν := MatrixLabelReference d m
  let B := ENNReal.ofReal (ProjectionNormScale m p H β R)
  refine ⟨?_, ?_, ?_⟩
  · intro E hE _
    rw [← hden]
    exact density_set_bound ν F hF hF0 p hp B hnorm E hE
  · rw [← hden]
    exact withDensity_absolutelyContinuous _ _
  · let ηc := ν.completion.withDensity (fun x => ENNReal.ofReal (F x))
    refine ⟨ηc, ?_, ?_, ?_⟩
    · intro E hE
      calc
        ηc E = ν.withDensity (fun x => ENNReal.ofReal (F x)) E :=
          withDensity_completion_apply ν F hF E hE
        _ = ProjectionLaw μ m E := congrArg (fun q => q E) hden
    · intro E hE _
      have hFc : @Measurable (NullMeasurableSpace _ ν) ℝ _ _ F :=
        hF.mono (original_le_completion ν) le_rfl
      have hnormc : eLpNorm F (p:ℝ≥0∞) ν.completion ≤ B := by
        erw [eLpNorm_completion ν F hF p (by omega)]
        exact hnorm
      exact density_set_bound ν.completion F hFc hF0 p hp B hnormc E hE
    · intro φ hφ hφ1
      have hFc : @Measurable (NullMeasurableSpace _ ν) ℝ _ _ F :=
        hF.mono (original_le_completion ν) le_rfl
      have hnormc : eLpNorm F (p:ℝ≥0∞) ν.completion ≤ B := by
        erw [eLpNorm_completion ν F hF p (by omega)]
        exact hnorm
      exact density_test_bound ν.completion F hFc hF0 p hp B hnormc
        (ProjectedEllipsoid z R) (isClosed_projectedEllipsoid z R).measurableSet.nullMeasurableSet
        hsupp φ hφ.aemeasurable hφ1
end MemoryPrecision


end

end OAI
