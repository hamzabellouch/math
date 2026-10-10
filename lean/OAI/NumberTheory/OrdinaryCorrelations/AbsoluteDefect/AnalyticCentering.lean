import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ReciprocalRangeMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWeight

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset Filter OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff
open scoped ContDiff

theorem analytic_centering (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hNP : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0<h) (τ C₀ T : ℝ) (hτ1 : 1<τ) (hτ2 : τ<2)
    (hC₀ : 1≤C₀) (hT : 0<T) (phi : ℝ→ℝ) (hφ : ContDiff ℝ ∞ phi)
    (hφb : ∀x,0≤phi x ∧ phi x≤1) (hφs : Function.support phi⊆Set.Icc (-T) T) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ B : ℝ in atTop,
    ∀ H : ℝ, ∀ D : Finset ℕ, Admissible B C₀ τ H D →
    ∀ a : ℕ→ℂ, (∀d∈D,‖a d‖≤1) →
    ∀ᶠ X : ℝ in atTop,
      ‖rawSum phi B D a f g h X-centeredSum phi B D a f g h X‖
        ≤ C*L₀ B*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B)*X := by
  have hφc : HasCompactSupport phi := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hφs
  obtain ⟨C,hC,hMain⟩:=dilation_rough_correlation h hh phi hφ hφc hφb
  have hCT : 0≤C₀*T := mul_nonneg (zero_le_one.trans hC₀) hT.le
  refine ⟨C+12+C₀*T,by linarith,?_⟩
  filter_upwards [hMain,eventually_ge_atTop (1:ℝ)] with B hB hB1
  intro H D hD a ha
  have hQ : 0<P₀ B := Real.exp_pos _
  have hB0 : 0<B := by linarith
  let β : ℝ := C*B^(-10001/10000:ℝ)+12*(J C₀ B:ℝ)/P₀ B
  have hβ : 0≤β := by dsimp [β];positivity
  have he (u:ℕ) (hu:u∈retainedSet B D) :
      ∀ᶠ X:ℝ in atTop,‖fiberSum phi B D a f g h u (X/u)‖≤β*(X/u) := by
    have huPos:=(retained_properties hD hu).1
    have huR : (0:ℝ)<u := by exact_mod_cast huPos
    have hscale:=retained_scale hB1 (by linarith:0<τ) hD hu
    have hZ (w:ℕ) (hw:w∈shiftSet B D u) : H/u<(w:ℝ) ∧ (w:ℝ)≤τ*(H/u) ∧
        SourceRoughFourier.IsRough (P₀ B) w := by
      have hs:=shift_properties hB1 hD hu hw
      exact ⟨hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1⟩
    have huQ : ∀p∈u.primeFactors,P₀ B≤(p:ℝ) := by
      intro p hp
      exact (prime_lower B hB1 ((retained_properties hD hu).2.1 hp)).le
    have hE:=hB τ hτ1 hτ2 (H/u) hscale (shiftSet B D u) hZ f g hf hg hfm hgm hNP
      ((core B).filter (fun p=>¬p∣u)) (fun p hp=>core_prime B (mem_filter.mp hp).1)
      (fiberCoeff a u) (fun w hw=>fiberCoeff_norm hB1 hD a ha hu hw) u (J C₀ B)
      huPos (retained_properties hD hu).2.2.1 huQ
    have ht : Tendsto (fun X:ℝ=>X/(u:ℝ)) atTop atTop := tendsto_id.atTop_div_const huR
    filter_upwards [ht.eventually hE] with X hX
    exact hX (coreMean B)
  have heAll:∀ᶠ X:ℝ in atTop,∀u∈retainedSet B D,
      ‖fiberSum phi B D a f g h u (X/u)‖≤β*(X/u) :=
    (eventually_all_finset (retainedSet B D)).mpr he
  filter_upwards [heAll,eventually_ge_atTop (0:ℝ)] with X hX hX0
  rw [norm_sub_rev,regroup_centered phi B D (admissible_facts hD) a f g h X hX0,add_sub_cancel_left]
  have hnorm : ‖∑u∈retainedSet B D,(divisorWeight B u:ℂ)*fiberSum phi B D a f g h u (X/u)‖≤
      ∑u∈retainedSet B D,divisorWeight B u*(β*(X/u)) := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro u hu
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (divisorWeight_pos B u).le]
    exact mul_le_mul_of_nonneg_left (hX u hu) (divisorWeight_pos B u).le
  have heq : (∑u∈retainedSet B D,divisorWeight B u*(β*(X/u)))=
      (β*X)*(∑u∈retainedSet B D,divisorWeight B u/(u:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    ring
  have hmain : ‖∑u∈retainedSet B D,(divisorWeight B u:ℂ)*fiberSum phi B D a f g h u (X/u)‖≤
      (β*X)*L₀ B := (hnorm.trans_eq heq).trans
        (mul_le_mul_of_nonneg_left (retained_mass hD) (mul_nonneg hβ hX0))
  apply hmain.trans
  have hc : β≤(C+12+C₀*T)*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B) := by
    dsimp [β]
    have hpow : 0≤B^(-10001/10000:ℝ):=Real.rpow_nonneg hB0.le _
    have hJ : 0≤(J C₀ B:ℝ)/P₀ B := div_nonneg (Nat.cast_nonneg _) hQ.le
    have hx : 12*(J C₀ B:ℝ)/P₀ B = 12*((J C₀ B:ℝ)/P₀ B) := by ring
    rw [hx]
    nlinarith [mul_nonneg hC.le hJ, mul_nonneg hCT (add_nonneg hpow hJ)]
  calc
    _ ≤((C+12+C₀*T)*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B)*X)*L₀ B := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hX0) (L₀_nonneg B)
    _ = _ := by ring
end OrdinaryAnalyticCentering

end

end OAI
