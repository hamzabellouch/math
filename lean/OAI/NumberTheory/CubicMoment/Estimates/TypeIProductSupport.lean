import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductLow

namespace OAI

/-! Remove only the proved zero terms when the detector's finite
squarefree envelope is put into a Type-I row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeProductEnvelope (Y : ℝ) : Finset Eisenstein :=
  (primaryElementBall Y).filter Squarefree

def productCenteredKernel (ℓ : ℤ) (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*centeredGauss n*normTwist t n*W (norm n/X)

lemma centeredGauss_zero_of_not_squarefree {n : Eisenstein} (hn : primary n)
    (hs : ¬Squarefree n) : centeredGauss n = 0 := by
  rw [centeredGauss,gauss_eq_zero_of_not_squarefree hn hs,
    idealMoebius_sq_complex,ite_eq_right hs]
  ring

lemma productCenteredKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (t : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then productCenteredKernel ℓ W X t n else 0) =
      productCenteredKernel ℓ W X t n := by
  by_cases hs : Squarefree n
  · by_cases hsize : norm n ≤ B*X
    · have hm : n ∈ squarefreeProductEnvelope (B*X) :=
        Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hsize⟩,hs⟩
      rw [ite_eq_left hm]
    · have hx : B < norm n/X := (lt_div_iff₀ hX).mpr (lt_of_not_ge hsize)
      simp only [productCenteredKernel,hW _ hx,mul_zero,ite_self]
  · simp only [productCenteredKernel,centeredGauss_zero_of_not_squarefree hn hs,
      mul_zero,zero_mul,ite_self]

theorem typeI_product_envelope_row (ℓ : ℤ) (W : ℝ → ℂ)
    {B X R U : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ)
    {r : Eisenstein} (hr : primary r) (hRr : R ≤ norm r) :
    (∑ u ∈ primaryElementBall (B*X),
      if r*u ∈ squarefreeProductEnvelope (B*X) then productCenteredKernel ℓ W X t (r*u) else 0) =
      ∑ u ∈ primaryElementBall (B*U), productCenteredKernel ℓ W X t (r*u) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hX : 0 < X := by rw [←hRU]; positivity
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hU.le hR
  have hsub : primaryElementBall (B*U) ⊆ primaryElementBall (B*X) := by
    intro u hu
    obtain ⟨hup,huB⟩ := mem_primaryElementBall.mp hu
    exact mem_primaryElementBall.mpr ⟨hup,huB.trans (mul_le_mul_of_nonneg_left hUX hB)⟩
  calc
    _ = ∑ u ∈ primaryElementBall (B*X), productCenteredKernel ℓ W X t (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact productCenteredKernel_envelope ℓ W hX hW t
        (primary_mul hr (mem_primaryElementBall.mp hu).1)
    _ = _ := by
      symm
      apply Finset.sum_subset hsub
      intro u hu hn
      obtain ⟨hup,huX⟩ := mem_primaryElementBall.mp hu
      have huB : B*U < norm u := lt_of_not_ge
        (fun huB => hn (mem_primaryElementBall.mpr ⟨hup,huB⟩))
      have hnX : B*X < norm (r*u) := by
        rw [norm_mul_eq,←hRU]
        calc
          B*(R*U) = R*(B*U) := by ring
          _ < R*norm u := mul_lt_mul_of_pos_left huB hRp
          _ ≤ norm r*norm u := mul_le_mul_of_nonneg_right hRr (norm_nonneg _)
      have hz := hW (norm (r*u)/X) ((lt_div_iff₀ hX).mpr hnX)
      simp only [productCenteredKernel,hz,mul_zero]

end CubicFirstMoment

end

end OAI
