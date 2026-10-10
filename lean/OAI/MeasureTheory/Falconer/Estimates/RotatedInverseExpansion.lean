import OAI.MeasureTheory.Falconer.Fourier.RotatedInverseSymbols

namespace OAI

/-! # Exact rotated inverse on the original two endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

noncomputable def rootInverseRadii (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ) :
    {b // b ∈ F} ⊕ {b // b ∈ F} → ℝ :=
  Sum.elim (fun b => descriptorMaskRadius N σ b) (fun b => descriptorMaskRadius N σ b)

noncomputable def rootInverseWeight (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    (a : RootInverseIndex m j F) : ℝ :=
  ∏ b, (rootInverseRadii F N σ b)⁻¹^((rootInverseTerm m j F a).jet b).order

namespace RotatedRootSymbols
variable {m j L : ℕ} {F : Finset PolicyDescriptor}
  {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} {A : ℝ}

theorem left_value (H : RotatedRootSymbols m j L F T A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U : ℝ) (a : RootInverseIndex m j F) (x : Space (m+3)) (w : Sphere (m+3)) :
    (H.left a).value Q ρ profile N σ J i S U x w =
      (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w) *
      ((U⁻¹:ℝ):ℂ)*normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T) w := by
  simp only [DescriptorJetSymbol.value,DescriptorJetSymbol.multiplier,descriptorJetProduct,H.left_spatial,
    H.left_angular,one_mul,id_eq]
  rw [H.left_jet a]
  rw [← Finset.prod_coe_sort]
  have hp : (∏ b : {b // b ∈ F},
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (rootInverseLeftJets m j F T a b).order (rootInverseLeftJets m j F T a b).vectors x w) =
      ∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w := by
    apply Finset.prod_congr rfl
    intro b _
    have hj : rootInverseLeftJets m j F T a b =
        ((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm := by
      unfold rootInverseLeftJets
      exact dite_eq_left b.property
    rw [hj]
    rfl
  change (∏ b : {b // b ∈ F}, _) * _ = _
  rw [hp]
  ring

theorem right_value (H : RotatedRootSymbols m j L F T A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U : ℝ) (a : RootInverseIndex m j F) (y : Space (m+3)) (w : Sphere (m+3)) :
    (H.right a).value Q ρ profile N σ J i S U y w =
      (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm).normalizedValue
        (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) y) w) *
      ((U⁻¹:ℝ):ℂ) := by
  simp only [DescriptorJetSymbol.value,DescriptorJetSymbol.multiplier,descriptorJetProduct,H.right_spatial,
    H.right_angular,one_mul,mul_one,id_eq]
  rw [H.right_jet a]
  rw [← Finset.prod_coe_sort]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  have hj : rootInverseRightJets m j F T a b =
      ((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm := by
    unfold rootInverseRightJets
    exact dite_eq_left b.property
  rw [hj]
  rfl

theorem expansion (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    {U : ℝ} (hU : 0 < U) (x y : Space (m+3)) (w : Sphere (m+3)) :
    rotatedInverseAmplitude m T (descriptorPairAmplitude Q ρ profile N σ J i F S x y) j w =
      ∑ a : RootInverseIndex m j F, ((rootInverseWeight m j F N σ a*(U*A)*U:ℝ):ℂ) *
        ((H.left a).value Q ρ profile N σ J i S U x w *
          (H.right a).value Q ρ profile N σ J i S U y w) := by
  let B : ({b // b ∈ F} ⊕ {b // b ∈ F}) → (Space (m+3) × Space (m+3)) → Space (m+3) → ℝ :=
    fun b xy => Sum.elim (fun c : {b // b ∈ F} => descriptorAmbientMask Q ρ profile N σ J i c (S c) xy.1)
      (fun c : {b // b ∈ F} => descriptorAmbientMask Q ρ profile N σ J i c (S c) xy.2) b
  have hB (b) (xy : Space (m+3) × Space (m+3)) : ContDiff ℝ ∞ (B b xy) := by
    cases b with
    | inl b => exact descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) xy.1
    | inr b => exact descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) xy.2
  have hp : descriptorPairAmplitude Q ρ profile N σ J i F S x y =
      fun z => ∏ b, (B b (x,y) z:ℂ) := by
    funext z
    simp only [B,descriptorPairAmplitude,descriptorAmbientProduct,Fintype.prod_sum_type,
      Sum.elim_inl,Sum.elim_inr,Complex.ofReal_prod]
    rw [← Finset.prod_coe_sort F,← Finset.prod_coe_sort F]
  rw [hp]
  have hr : ∀ b, rootInverseRadii F N σ b ≠ 0 := by
    intro b
    cases b with
    | inl b => exact (descriptorMaskRadius_pos N σ b).ne'
    | inr b => exact (descriptorMaskRadius_pos N σ b).ne'
  rw [MaskJetExpansion.rotatedInverseAmplitude_product_radius_jets m j T _ hr B hB (x,y) w]
  apply Finset.sum_congr rfl
  intro a _
  change (rootInverseTerm m j F a).radiusCoefficient (rootInverseRadii F N σ) (T w) *
      (∏ b, (((rootInverseTerm m j F a).jet b).mapIsometry T.symm).normalizedValue
        (rootInverseRadii F N σ b) (B b (x,y)) w) = _
  rw [MaskJetTerm.radiusCoefficient]
  change (rootInverseTerm m j F a).coefficient (T w) * (rootInverseWeight m j F N σ a : ℂ) *
      (∏ b, (((rootInverseTerm m j F a).jet b).mapIsometry T.symm).normalizedValue
        (rootInverseRadii F N σ b) (B b (x,y)) w) = _
  rw [Fintype.prod_sum_type,H.left_value,H.right_value]
  simp only [rootInverseRadii,B,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_mul]
  have hn := normalizedAngular_restore hA ((rootInverseTerm m j F a).coefficient ∘ T) (w:Space (m+3))
  simp only [Function.comp_apply] at hn
  have hu : (U:ℂ)*(U⁻¹:ℝ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hU.ne',Complex.ofReal_one]
  rw [← hn]
  symm
  calc
    _ = ((A:ℂ)*normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T) w) *
        (rootInverseWeight m j F N σ a : ℂ) *
        ((∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inl b)).mapIsometry T.symm).normalizedValue
          (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) x) w) *
        (∏ b : {b // b ∈ F}, (((rootInverseTerm m j F a).jet (.inr b)).mapIsometry T.symm).normalizedValue
          (descriptorMaskRadius N σ b) (descriptorAmbientMask Q ρ profile N σ J i b (S b) y) w)) *
        ((U:ℂ)*(U⁻¹:ℝ))*((U:ℂ)*(U⁻¹:ℝ)) := by ring
    _ = _ := by rw [hu]; ring

end RotatedRootSymbols
end Falconer

end OAI
