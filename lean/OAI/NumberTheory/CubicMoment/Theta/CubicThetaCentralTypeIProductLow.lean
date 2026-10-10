import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductLow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralTypeILowIntegral

namespace OAI

/-! Low Type I for the actual product-norm envelope. Bounded dilation
supplies the selected inner weights; it is not an additional hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem typeI_product_low_integral_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {A : ℝ} (hA : 0 ≤ A) (k Ct : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (P : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U H X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
      1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ P, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖productTypeILowIntegral w P α W ℓ (Real.exp hW.radius) X U H
        ((1+Real.log X)^Ct) X₀‖ ≤ K*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  let δ := {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2}
  let V : (γ × δ) × {X : ℝ // 1 ≤ X} → ℝ → ℂ :=
    fun i x => W i.1.1 ((i.1.2:ℝ)*x)
  have hV : LogarithmicWeightFamily (fun i : (γ × δ) × {X : ℝ // 1 ≤ X} => (i.2:ℝ)) V :=
    (hW.logDilate (Real.log 2) (Real.log_nonneg (by norm_num))).logarithmicWithLength
  have hB : 1 ≤ Real.exp hW.radius := Real.one_le_exp_iff.mpr hW.radius_nonneg
  obtain ⟨K,hK,hbound⟩ := typeI_low_integral_bound_actual  hV ℓ hGamma hB hA k Ct
  refine ⟨K,hK,?_⟩
  intro w P α X R U H X₀ hX hlog hBX hR hU hRU hRhi hP hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  let s : Eisenstein → δ := fun r => if hr : r ∈ P then
    ⟨norm r/R,log_dyad_ratio hRp (by norm_num) (hP r hr).2.1 (hP r hr).2.2⟩
    else ⟨1,by simp; exact Real.log_nonneg (by norm_num)⟩
  let v : Eisenstein → (γ × δ) × {X : ℝ // 1 ≤ X} :=
    fun r => ((w r,s r),⟨X,by linarith⟩)
  have hv (r : Eisenstein) (hr : r ∈ P) :
      V (v r) = fun x => W (w r) ((norm r/R)*x) := by
    funext x
    simp only [V,v,s,dite_eq_left hr]
  have hcut (r : Eisenstein) (hr : r ∈ P) (x : ℝ)
      (hx : Real.exp hW.radius < x) : V (v r) x = 0 := by
    rw [hv r hr]
    apply hW.upper_support (w r)
    have hratio : 1 ≤ norm r/R := (le_div_iff₀ hRp).mpr (by simpa using (hP r hr).2.1)
    exact hx.trans_le (le_mul_of_one_le_left (by linarith [Real.exp_pos hW.radius]) hratio)
  have hb := hbound v P α X R U H X₀ hX hlog hBX hR hU hRU hRhi hP
    (fun _ _ => rfl) hcut hα
  have he (t : ℝ) :
      (∑ r ∈ P, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*U),
        theta ℓ (r*u)*centeredGauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X)) =
      ∑ r ∈ P, (α r*normTwist t r)*lowTwistedTypeIRow r ℓ (V (v r)) U t := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [lowTwistedTypeIRow_finite r ℓ (V (v r)) hUp (hcut r hr) t,
      Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have harg : (norm r/R)*(norm u/U) = norm (r*u)/X := by
      rw [norm_mul_eq,←hRU]
      field_simp
    have hp : normTwist t (r*u) = normTwist t r*mellinPhase t (norm u) := by
      exact normTwist_mul t (primary_ne_zero (hP r hr).1)
        (primary_ne_zero (mem_primaryElementBall.mp hu).1)
    simp only [hv r hr,harg]
    rw [hp]
    ring
  have heq : productTypeILowIntegral w P α W ℓ (Real.exp hW.radius) X U H
      ((1+Real.log X)^Ct) X₀ =
      lowTypeIIntegral v P α V ℓ U H ((1+Real.log X)^Ct) X₀ := by
    unfold productTypeILowIntegral lowTypeIIntegral
    apply integral_congr_ae
    filter_upwards with t
    rw [he t]
  rwa [heq]

end CubicFirstMoment

end

end OAI
