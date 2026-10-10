import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSmallLow
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLargeLow
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortModelLow
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLevelMass
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseSplit
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAngularOuter

namespace OAI

/-! The fixed nonzero-angular low-height Type-I estimate. The short and
long inverse sums are actual finite sums, and the coefficient masses
are deduced from the literal primary-divisor bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem angular_typeI_low_squarefree_of_published
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨D,hD,hcoef⟩ := metaplectic_divisor_coefficient_power (by norm_num : 0 < κ) hA k
  obtain ⟨KS,hKS,hshort⟩ := hW.metaplectic_short_low_power hV ℓ hGamma
    (show 0 ≤ 36*D by positivity)
  obtain ⟨KM,hKM,hmodel⟩ := hW.angular_model_low_power hℓ (show 0 ≤ 36*D by positivity)
  obtain ⟨KC,hKC,hcount⟩ := hW.metaplectic_long_small_power hB (show 0 ≤ 36*D by positivity)
  obtain ⟨KL,hKL,hlarge⟩ := hW.metaplectic_long_large_power hB (show 0 ≤ 36*D^2 by positivity)
  refine ⟨KS+KM+KC+KL,by positivity,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hB0 : 0 ≤ B := by linarith
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hp (r : Eisenstein) (hr : r ∈ S) : primary r := (hS r hr).1
  have hsn (r : Eisenstein) (hr : r ∈ S) : primary r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.2.2⟩
  have hsfull (r : Eisenstein) (hr : r ∈ S) : primary r ∧ Squarefree r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.2⟩
  have hym (r : Eisenstein) (hr : r ∈ S) : Y (w r) ≤ X := (hY r hr).le
  have hab (r : Eisenstein) (hr : r ∈ S) : ‖α r‖ ≤ D*X^κ :=
    hcoef r (hp r hr) X hX1 ((hS r hr).2.2.2.trans (by linarith)) (α r) (hα r hr)
  obtain ⟨hm1,hm2⟩ := metaplectic_level_masses S α hRp.le (by positivity) hsn hab
  have hm1' : (∑ r ∈ S, ‖α r‖) ≤ (36*D)*R*X^κ := by
    convert hm1 using 1
    ring
  have hm2' : (∑ r ∈ S, ‖α r‖^2) ≤ (36*D^2)*R*X^(2*κ) := by
    apply hm2.trans_eq
    have hx : (X^κ)^2 = X^(2*κ) := by
      rw [←Real.rpow_mul_natCast hXp.le]
      norm_num
    rw [mul_pow,hx]
    ring
  let C : ℝ := if R ≤ X^(2/5:ℝ) then X^(13/100:ℝ) else X^(1/50:ℝ)
  have hCpos : 0 < C := by dsimp [C]; split_ifs <;> positivity
  have hCX : C ≤ X := by
    dsimp [C]
    split_ifs
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (13/100:ℝ) ≤ 1 by norm_num)
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (1/50:ℝ) ≤ 1 by norm_num)
  have hscale : R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
    dsimp [C]
    split_ifs with hs
    · exact metaplectic_short_small_power hX1 hRp.le hs
    · exact metaplectic_short_large_power hX1 hRp.le hRhi
  have hs := hshort w S α X R U C hX hR hU hRU hCpos.le hCX hscale hsfull hY hm1'
  have hm := hmodel w S α X R U hX hR hU hRU hRhi
    (fun r hr => ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.1⟩) hym hm1'
  have hl : ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2)‖ ≤
      (KC+KL)*X^(41/50:ℝ) := by
    dsimp [C]
    split_ifs with hsmall
    · exact (hcount w S α ℓ X R U hX hBX hR hU hRU hp hym hcut hm1').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · exact (hlarge w S α ℓ X R U hX hBX hR hU hRU (le_of_lt (lt_of_not_ge hsmall))
        hRhi hsn hym hcut hm2').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)) =
      (∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C)+
      (∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2))-
      (∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [metaplectic_angular_inverse_split r hℓ (W (w r)) hUp hB0 hBU
      (hCX.trans (by nlinarith : X ≤ X^2)) (hcut r hr)]
    ring
  rw [he]
  calc
    _ ≤ (‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖+
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2)‖)+
      ‖∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ KS*X^(41/50:ℝ)+(KC+KL)*X^(41/50:ℝ)+KM*X^(41/50:ℝ) :=
      add_le_add (add_le_add hs hl) hm
    _ = (KS+KM+KC+KL)*X^(41/50:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)

theorem angular_typeI_low_of_published
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := angular_typeI_low_squarefree_of_published hV hW ℓ hℓ hGamma hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  let T := S.filter Squarefree
  have hT (r : Eisenstein) (hr : r ∈ T) : r ∈ S ∧ Squarefree r := Finset.mem_filter.mp hr
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
      angularSmoothModel r ℓ (W (w r)) U)) =
      ∑ r ∈ T, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hsf : ¬Squarefree r := fun hs => hn (Finset.mem_filter.mpr ⟨hr,hs⟩)
    rw [metaplecticAngularSmoothSum_zero_of_not_squarefree (hS r hr).1 hsf,
      angularSmoothModel_zero_of_not_squarefree hsf,sub_self,mul_zero]
  rw [he]
  exact hbound w T α X R U hX hBX hR hU hRU hRhi
    (fun r hr => ⟨(hS r (hT r hr).1).1,(hT r hr).2,(hS r (hT r hr).1).2⟩)
    (fun r hr => hY r (hT r hr).1) (fun r hr => hcut r (hT r hr).1)
    (fun r hr => hα r (hT r hr).1)

end CubicFirstMoment

end

end OAI
