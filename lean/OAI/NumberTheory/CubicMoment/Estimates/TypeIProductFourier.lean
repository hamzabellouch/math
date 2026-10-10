import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductSupport
import OAI.NumberTheory.CubicMoment.Estimates.PrimeLowHeight

namespace OAI

/-! The product-envelope Type-I integral equals the literal finite
height-Fourier kernel used in the detector decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def centeredHeightKernel (ℓ : ℤ) (W : ℝ → ℂ) (H T X X₀ : ℝ)
    (n : Eisenstein) : ℂ :=
  theta ℓ n*centeredGauss n*W (norm n/X)*
    heightFourierIntegral (lowHeightWeight H T) (Real.log (norm n)-Real.log X₀)

lemma centeredHeightKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (H T X₀ : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then centeredHeightKernel ℓ W H T X X₀ n else 0) =
      centeredHeightKernel ℓ W H T X X₀ n := by
  have he := congrArg (fun z : ℂ => z*heightFourierIntegral (lowHeightWeight H T)
    (Real.log (norm n)-Real.log X₀)) (productCenteredKernel_envelope ℓ W hX hW 0 hn)
  simpa only [ite_mul,zero_mul,productCenteredKernel,normTwist,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero,mul_one,centeredHeightKernel] using he

theorem typeI_height_envelope_row (ℓ : ℤ) (W : ℝ → ℂ)
    {B X R U : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hW : ∀ x : ℝ, B < x → W x = 0) (H T X₀ : ℝ)
    {r : Eisenstein} (hr : primary r) (hRr : R ≤ norm r) :
    (∑ u ∈ primaryElementBall (B*X),
      if r*u ∈ squarefreeProductEnvelope (B*X) then centeredHeightKernel ℓ W H T X X₀ (r*u) else 0) =
      ∑ u ∈ primaryElementBall (B*U), centeredHeightKernel ℓ W H T X X₀ (r*u) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hX : 0 < X := by rw [←hRU]; positivity
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hU.le hR
  have hsub : primaryElementBall (B*U) ⊆ primaryElementBall (B*X) := by
    intro u hu
    obtain ⟨hup,huB⟩ := mem_primaryElementBall.mp hu
    exact mem_primaryElementBall.mpr ⟨hup,huB.trans (mul_le_mul_of_nonneg_left hUX hB)⟩
  calc
    _ = ∑ u ∈ primaryElementBall (B*X), centeredHeightKernel ℓ W H T X X₀ (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact centeredHeightKernel_envelope ℓ W hX hW H T X₀
        (primary_mul hr (mem_primaryElementBall.mp hu).1)
    _ = _ := by
      symm
      apply Finset.sum_subset hsub
      intro u hu hn
      have hup := (mem_primaryElementBall.mp hu).1
      have huB : B*U < norm u := lt_of_not_ge
        (fun huB => hn (mem_primaryElementBall.mpr ⟨hup,huB⟩))
      have hnX : B*X < norm (r*u) := by
        rw [norm_mul_eq,←hRU]
        calc
          B*(R*U) = R*(B*U) := by ring
          _ < R*norm u := mul_lt_mul_of_pos_left huB hRp
          _ ≤ norm r*norm u := mul_le_mul_of_nonneg_right hRr (norm_nonneg _)
      have hz := hW (norm (r*u)/X) ((lt_div_iff₀ hX).mpr hnX)
      simp only [centeredHeightKernel,hz,mul_zero,zero_mul]

theorem productTypeILowIntegral_fourier {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U T X₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    productTypeILowIntegral w P α W ℓ B X U H T X₀ =
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        centeredHeightKernel ℓ (W (w r)) H T X X₀ (r*u) := by
  let Q := primaryElementBall (B*U)
  let c : Eisenstein × Eisenstein → ℂ := fun q =>
    α q.1*(theta ℓ (q.1*q.2)*centeredGauss (q.1*q.2)*W (w q.1) (norm (q.1*q.2)/X))
  have hb := height_norm_polynomial_integral (P.product Q) c (fun q => q.1*q.2)
    (lowHeightWeight H T) (lowHeightWeight_integrable hH T) (Real.log X₀)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hb
  calc
    _ = ∫ t : ℝ, (lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ r ∈ P, ∑ u ∈ Q, c (r,u)*normTwist t (r*u) := by
      unfold productTypeILowIntegral
      apply integral_congr_ae
      filter_upwards with t
      simp only [Finset.mul_sum,c,Q]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ r ∈ P, ∑ u ∈ Q,
        c (r,u)*heightFourierIntegral (lowHeightWeight H T)
          (Real.log (norm (r*u))-Real.log X₀) := hb.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp [c,Q,centeredHeightKernel]
      ring

end CubicFirstMoment

end

end OAI
