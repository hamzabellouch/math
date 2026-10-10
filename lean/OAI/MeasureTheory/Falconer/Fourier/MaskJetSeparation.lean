import OAI.MeasureTheory.Falconer.Fourier.InverseJetSupport
import OAI.MeasureTheory.Falconer.Fourier.MaskJetCount

namespace OAI

/-! # Finite normalized endpoint factors for the actual inverse

The original individual-mask jets remain in the smooth endpoint factors.
All inverse-radius powers are kept in a separate scalar weight per term.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
theorem normalizedValue_contDiff {d : ℕ} (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (j.normalizedValue r f) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j.order => Space d) ℝ j.vectors).contDiff.comp
      (hf.iteratedFDeriv_right (by simp))))
end MaskJetIndex

namespace SmoothSeparation
variable {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scaleTerms (S : SmoothSeparation X Y E) (c : S.index → ℂ) :
    SmoothSeparation X Y E where
  index := S.index
  finite := S.finite
  left := fun i x z => c i*S.left i x z
  right := S.right
  left_smooth := fun i x => contDiff_const.mul (S.left_smooth i x)
  right_smooth := S.right_smooth

theorem scaleTerms_value (S : SmoothSeparation X Y E) (c : S.index → ℂ)
    (x : X) (y : Y) (z : E) :
    (S.scaleTerms c).value x y z = ∑ i : S.index, c i*(S.left i x z*S.right i y z) := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

end SmoothSeparation

variable {ι τ : Type} {X Y : Type*} [Fintype ι] [Fintype τ]
  [DecidableEq ι] [DecidableEq τ]

noncomputable abbrev inversePairJets (m j : ℕ) :
    MaskJetExpansion (ι ⊕ τ) (m+3) (Space (m+3)) :=
  (MaskJetExpansion.product : MaskJetExpansion (ι ⊕ τ) (m+3) (Space (m+3))).inverse m j

noncomputable def inverseJetRadiusWeight (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index) : ℝ :=
  ∏ i, (r i)⁻¹^(((inversePairJets (ι := ι) (τ := τ) m j).term a).jet i).order

noncomputable def inverseJetSeparation (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y)) :
    SmoothSeparation X Y (Space (m+3)) where
  index := (inversePairJets (ι := ι) (τ := τ) m j).index
  finite := inferInstance
  left := fun a x z => ((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient z *
    ∏ i, (((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inl i)).normalizedValue (r (.inl i)) (B i x) z
  right := fun a y z =>
    ∏ i, (((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inr i)).normalizedValue (r (.inr i)) (C i y) z
  left_smooth := fun a x => ((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient_smooth.mul
    (contDiff_prod (fun i _ => MaskJetIndex.normalizedValue_contDiff _ _ _ (hB i x)))
  right_smooth := fun _a y =>
    contDiff_prod (fun i _ => MaskJetIndex.normalizedValue_contDiff _ _ _ (hC i y))

theorem inverseJetSeparation_left (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index) (x : X) (z : Space (m+3)) :
    (inverseJetSeparation m j r B C hB hC).left a x z =
      ((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient z *
        ∏ i, (((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inl i)).normalizedValue
          (r (.inl i)) (B i x) z := rfl

theorem inverseJetSeparation_right (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index) (y : Y) (z : Space (m+3)) :
    (inverseJetSeparation m j r B C hB hC).right a y z =
      ∏ i, (((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inr i)).normalizedValue
        (r (.inr i)) (C i y) z := rfl

theorem inverseJetSeparation_exact (m j : ℕ) (r : ι ⊕ τ → ℝ) (hr : ∀ i, r i ≠ 0)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (x : X) (y : Y) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => (∏ i, (B i x z : ℂ))*(∏ i, (C i y z : ℂ))) j e =
      ((inverseJetSeparation m j r B C hB hC).scaleTerms
        (fun a => (inverseJetRadiusWeight m j r a : ℂ))).value x y e := by
  rw [MaskJetExpansion.localInverseAmplitude_endpoint_radius_jets_global m j r hr B C hB hC x y e,
    SmoothSeparation.scaleTerms_value]
  apply Finset.sum_congr rfl
  intro a _
  rw [inverseJetSeparation_left,inverseJetSeparation_right]
  change (((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient e *
      (inverseJetRadiusWeight m j r a : ℂ)) * _ * _ =
    (inverseJetRadiusWeight m j r a : ℂ) *
      ((((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient e * _) * _)
  ring

theorem inverseJetRadiusWeight_nonneg (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (hr : ∀ i, 0 < r i) (a : (inversePairJets (ι := ι) (τ := τ) m j).index) :
    0 ≤ inverseJetRadiusWeight m j r a :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)

theorem inverseJetRadiusWeight_le (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D) (hscale : ∀ i, (r i)⁻¹ ≤ D)
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index) :
    inverseJetRadiusWeight m j r a ≤ D^(2*j) := by
  have horder := (MaskJetExpansion.product_hasOrder (ι := ι ⊕ τ) (d := m+3)).inverse j a
  calc
    _ ≤ ∏ i, D^(((inversePairJets (ι := ι) (τ := τ) m j).term a).jet i).order := by
      apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)
      intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hr i).le) (hscale i) _
    _ = D^((inversePairJets (ι := ι) (τ := τ) m j).term a).order := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ D^(2*j) := pow_le_pow_right₀ hD (by simpa only [Nat.zero_add] using horder)

theorem inverseJetSeparation_card (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (B : ι → X → Space (m+3) → ℝ) (C : τ → Y → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y)) :
    Fintype.card (inverseJetSeparation m j r B C hB hC).index =
      MaskJetExpansion.inverseMultiplicity (m+2) j *
        (1+(Fintype.card ι+Fintype.card τ)*(m+3))^(2*j) := by
  change Fintype.card (inversePairJets (ι := ι) (τ := τ) m j).index = _
  rw [MaskJetExpansion.card_inverse_product,Fintype.card_sum]

theorem inverseJetSeparation_left_descriptor (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (f : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3)))
    (hr : ∀ a, r (.inl a) = descriptorMaskRadius N σ (b a))
    (C : τ → Y → Space (m+3) → ℝ) (hC : ∀ a y, ContDiff ℝ ∞ (C a y))
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (inverseJetSeparation m j r
      (fun a x => descriptorAmbientMask Q ρ f N σ J i (b a) (S (b a)) x) C
      (fun a x => descriptorAmbientMask_contDiff Q ρ f N σ J i (b a) (S (b a)) x) hC).left a x w =
      normalizedDescriptorJetFactor Q ρ f N σ J i b S
        (fun k => ((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inl k))
        (fun w => ((inversePairJets (ι := ι) (τ := τ) m j).term a).coefficient w) x w := by
  rw [inverseJetSeparation_left]
  unfold normalizedDescriptorJetFactor
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [hr k]

theorem inverseJetSeparation_right_descriptor (m j : ℕ) (r : ι ⊕ τ → ℝ)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (f : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : τ → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3)))
    (hr : ∀ a, r (.inr a) = descriptorMaskRadius N σ (b a))
    (B : ι → X → Space (m+3) → ℝ) (hB : ∀ a x, ContDiff ℝ ∞ (B a x))
    (a : (inversePairJets (ι := ι) (τ := τ) m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (inverseJetSeparation m j r B
      (fun a x => descriptorAmbientMask Q ρ f N σ J i (b a) (S (b a)) x) hB
      (fun a x => descriptorAmbientMask_contDiff Q ρ f N σ J i (b a) (S (b a)) x)).right a x w =
      normalizedDescriptorJetFactor Q ρ f N σ J i b S
        (fun k => ((inversePairJets (ι := ι) (τ := τ) m j).term a).jet (.inr k))
        (fun _ => 1) x w := by
  rw [inverseJetSeparation_right]
  unfold normalizedDescriptorJetFactor
  rw [one_mul]
  apply Finset.prod_congr rfl
  intro k _
  rw [hr k]

end Falconer

end OAI
