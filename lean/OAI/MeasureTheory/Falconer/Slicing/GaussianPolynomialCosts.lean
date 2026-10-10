import OAI.MeasureTheory.Falconer.Slicing.GaussianOriginalCosts
import OAI.MeasureTheory.Falconer.Slicing.GaussianScaleBudget

namespace OAI

/-! # Polynomial slice thresholds with the two actual radial cost tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

private theorem polynomial_cost_order (a b c d e : ℝ≥0∞) :
    (a+e)+b+c+d = a+b+c+d+e := by ac_rfl

theorem gaussian_select_polynomial_costs
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (Q : ℝ≥0∞)
    {K C S N R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i)) (hQ : Q ≤ ENNReal.ofReal C)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (i₀ : ι) (hi₀ : D < r i₀)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {u | i ∈ J u})
    (a : κ → Space (n+1)) (hJN : ∀ u, ((J u).card : ℝ≥0∞) ≤ ENNReal.ofReal N)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    (C₁ C₂ : (Fin h → Space (n+1)) → ℝ≥0∞) (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (t₁ t₂ b : ℝ≥0∞) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ))+
      (ENNReal.ofReal (K^6*w i₀)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)))*
        ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₁)+
      (ENNReal.ofReal (K^6*w i₀)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)))*
        ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₂) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      C₁ A < t₁ ∧ C₂ A < t₂ ∧ b < gaussianPrunedPairMass μ ν δ r
        (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i))
        (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R
          (ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h)))) true) (A,z) := by
  have hw₀ := hw i₀
  apply gaussian_select_original_costs B hB μ ν hμ hδ hδρ hwB r
    (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i)) CP CD
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 6) (hw i)))
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 3) (hv i))) i₀ hi₀
    (ENNReal.ofReal_pos.mpr (pow_pos hK 3)) ENNReal.ofReal_ne_top
    hpoint hdir hmoment E hE J hJ a hR.le hJN
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top
    C₁ C₂ hC₁ hC₂ t₁ t₂ b ht₁ ht₂ ht₁top ht₂top
  have hc := gaussian_four_polynomial_costs hK hS (hw i₀) hN hR hcard hC hlarge
    w v hw hv CP CD hCP hCD h hbase hQ
  apply lt_of_le_of_lt _ (hc.trans_le hmean)
  calc
    _ = (b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ))+
        (ENNReal.ofReal (K^6*w i₀)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)))*
          ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₁)+
        (ENNReal.ofReal (K^6*w i₀)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)))*
          ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₂)) +
        (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*((ENNReal.ofReal (K^3))⁻¹*Q) +
        ENNReal.ofReal (K^6*w i₀)*(ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) :=
      polynomial_cost_order _ _ _ _ _
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add le_rfl (mul_le_mul' hfactor le_rfl))
        (mul_le_mul' hfactor le_rfl)) le_rfl

end Falconer

end OAI
