import OAI.MeasureTheory.Falconer.Fourier.DescriptorInverseJets
import OAI.MeasureTheory.Falconer.Fourier.DescriptorJetMeasurable

namespace OAI

/-! # Global original-point factors for the inverse expansion

Every inverse coefficient vanishes off the fixed patch. Thus its individual
mask jets can be evaluated at the original sphere point globally, and each
resulting descriptor factor retains every original angular good condition.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]

theorem stationaryJet_coefficient_eq_zero (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (a : (S.stationaryJet m j).index)
    (e : Space (m+3)) (he : stationaryPatchMask m e = 0) :
    ((S.stationaryJet m j).term a).coefficient e = 0 := by
  change SmoothSeparation.stationaryJetMultiplier m j e * _ = 0
  rw [show SmoothSeparation.stationaryJetMultiplier m j e = 0 by
    simp only [SmoothSeparation.stationaryJetMultiplier,he,Complex.ofReal_zero,zero_mul],zero_mul]

theorem inverse_coefficient_eq_zero (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) (a : (S.inverse m j).index)
    (e : Space (m+3)) (he : stationaryPatchMask m e = 0) :
    ((S.inverse m j).term a).coefficient e = 0 := by
  revert a
  cases j with
  | zero =>
    rw [MaskJetExpansion.inverse]
    intro a
    change ((sphereStationaryConstant (m+2))⁻¹*(stationaryPatchMask m e : ℂ))*_ = 0
    simp only [he,Complex.ofReal_zero,mul_zero,zero_mul]
  | succ j =>
    rw [MaskJetExpansion.inverse]
    intro a
    change -(sphereStationaryConstant (m+2))⁻¹ *
      (((S.inverse m (j-a.1)).stationaryJet m ((a.1:ℕ)+1)).term a.2).coefficient e = 0
    rw [stationaryJet_coefficient_eq_zero _ _ _ _ e he,mul_zero]

theorem inverse_product_term_radius_normalized (m j : ℕ)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    ∀ a : T.index,
      (T.term a).value (fun i x z => (B i x z : ℂ)) x e =
        (T.term a).radiusCoefficient r e *
          ∏ i, ((T.term a).jet i).normalizedValue (r i) (B i x) e := by
  intro T a
  by_cases he : stationaryPatchMask m e = 0
  · have hc : (T.term a).coefficient e = 0 := inverse_coefficient_eq_zero m j product a e he
    simp only [MaskJetTerm.value,MaskJetTerm.radiusCoefficient,hc,zero_mul]
  · have hnear : ‖(e : Space (m+3))-
        (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 :=
      (poleCutoff_support _ _ he).le.trans (by norm_num)
    exact (T.term a).value_radius_normalized r hr B hB x e e
      ((product_hasPointAt (ι := ι) (e : Space (m+3))).inverse hnear j a)

/-- The finite normalized expansion holds everywhere on the sphere. -/
theorem localInverseAmplitude_product_radius_jets_global (m j : ℕ)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    localInverseAmplitude m (fun z => ∏ i, (B i x z : ℂ)) j e =
      ∑ a : T.index, (T.term a).radiusCoefficient r e *
        ∏ i, ((T.term a).jet i).normalizedValue (r i) (B i x) e := by
  intro T
  have hcomplex (i : ι) (x : X) : ContDiff ℝ ∞ (fun z => (B i x z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hB i x)
  have hvalue := inverse_value m j product (fun i x z => (B i x z : ℂ)) hcomplex x e
  have hproduct : (product : MaskJetExpansion ι (m+3) (Space (m+3))).value
      (fun i x z => (B i x z : ℂ)) x = fun z => ∏ i, (B i x z : ℂ) :=
    funext (product_value _ x)
  rw [hproduct] at hvalue
  rw [← hvalue]
  apply Finset.sum_congr rfl
  intro a _
  exact inverse_product_term_radius_normalized m j r hr B hB x e a

theorem localInverseAmplitude_endpoint_radius_jets_global
    {τ : Type} {Y : Type*} [Fintype τ] [DecidableEq τ] (m j : ℕ)
    (r : ι ⊕ τ → ℝ) (hr : ∀ i, r i ≠ 0)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (x : X) (y : Y) (e : Sphere (m+3)) :
    let T := (product : MaskJetExpansion (ι ⊕ τ) (m+3) (Space (m+3))).inverse m j
    localInverseAmplitude m
      (fun z => (∏ i, (B i x z : ℂ))*(∏ i, (C i y z : ℂ))) j e =
      ∑ a : T.index, (T.term a).radiusCoefficient r e *
        (∏ i, ((T.term a).jet (.inl i)).normalizedValue (r (.inl i)) (B i x) e) *
        (∏ i, ((T.term a).jet (.inr i)).normalizedValue (r (.inr i)) (C i y) e) := by
  intro T
  let F : ι ⊕ τ → X × Y → Space (m+3) → ℝ :=
    fun i xy z => Sum.elim (fun a => B a xy.1 z) (fun b => C b xy.2 z) i
  have hF (i : ι ⊕ τ) (xy : X × Y) : ContDiff ℝ ∞ (F i xy) := by
    cases i with
    | inl i => exact hB i xy.1
    | inr i => exact hC i xy.2
  have heq : (fun z => (∏ i, (B i x z : ℂ))*(∏ i, (C i y z : ℂ))) =
      fun z => ∏ i : ι ⊕ τ, (F i (x,y) z : ℂ) := by
    funext z
    rw [Fintype.prod_sum_type]
    rfl
  rw [heq,localInverseAmplitude_product_radius_jets_global m j r hr F hF (x,y) e]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_sum_type,mul_assoc]
  rfl

end MaskJetExpansion

noncomputable def normalizedDescriptorJetFactor {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ)
    (J i : ℕ) (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (k : ι → MaskJetIndex d) (q : Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  q w * ∏ a, (k a).normalizedValue (descriptorMaskRadius N σ (b a))
    (descriptorAmbientMask Q ρ m N σ J i (b a) (S (b a)) x) w

theorem normalizedDescriptorJetFactor_eq_product {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ)
    (J i : ℕ) (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (k : ι → MaskJetIndex d) (q : Sphere d → ℂ) (x : Space d) (w : Sphere d) :
    normalizedDescriptorJetFactor Q ρ m N σ J i b S k q x w =
      q w * descriptorJetProduct Q ρ m N σ J i Finset.univ b S
        (fun a => (k a).order) (fun a _ => (k a).vectors) x w := rfl

theorem normalizedDescriptorJetFactor_support {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ)
    (J i : ℕ) (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (k : ι → MaskJetIndex d) (q : Sphere d → ℂ) (x : Space d) (w : Sphere d)
    (h : normalizedDescriptorJetFactor Q ρ m N σ J i b S k q x w ≠ 0) :
    ∀ a, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) (b a) := by
  rw [normalizedDescriptorJetFactor_eq_product] at h
  have hp := (mul_ne_zero_iff.mp h).2
  intro a
  exact descriptorJetProduct_support Q ρ m N σ J i Finset.univ b S
    (fun a => (k a).order) (fun a _ => (k a).vectors) x w hp a (Finset.mem_univ a)

theorem normalizedDescriptorJetFactor_measurable {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ)
    (J i : ℕ) (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (k : ι → MaskJetIndex d) (q : Sphere d → ℂ) (hq : Measurable q) :
    Measurable (Function.uncurry (normalizedDescriptorJetFactor Q ρ m N σ J i b S k q)) := by
  have hp := descriptorJetProduct_measurable Q ρ m N σ J i Finset.univ b S
    (fun a => (k a).order) (fun a _ => (k a).vectors) (fun _ _ => measurable_const)
  convert (hq.comp measurable_snd).mul hp using 1
  rfl

end Falconer

end OAI
