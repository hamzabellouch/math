import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
import OAI.NumberTheory.DirichletL.Moments.Forcing

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExceptionalEnergy
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem forcing_finite_energy (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M D : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ C*Z^M)
    (f : O → ℂ) (hf : ∀ z ∈ rows, ‖f z‖ ≤ D) :
    (∑ z ∈ rows, ‖f z‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*C^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*D^2 := by
  have hc := actual_forcing_exceptional_count p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z C M hZ hC hN
  calc
    _ ≤ ∑ _z ∈ rows, D^2 := Finset.sum_le_sum (fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hf z hz) 2)
    _ = (rows.card:ℝ)*D^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg D)

theorem exceptional_slots_energy (Q : Ideal O) (hQ0 : Q ≠ 0)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (p : ι → O), (∀ i, Prime (Ideal.span {p i})) →
      Function.Injective (fun i => Ideal.span {p i}) →
      ∀ (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter),
      ∀ m e : O, m ≠ 0 → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      elementCoeff η e ≠ 0 → ∀ rows : Finset O,
      (∀ z ∈ rows, z ≠ 0) →
      (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
        (childCharacter η χ) Q m (movingElement p c d V) z) →
      (∀ z ∈ rows, (HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1
        (movingElement p c d V*z):ℝ) ≤ Z^B) →
      (∀ i ∈ forcingSet c d V,
        ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
        IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e}) →
      ∀ Cr Mrow : ℝ, 0 ≤ Cr →
      (∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Cr*Z^Mrow) →
      ∀ (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P b Ms : κ → ℝ),
      (∀ i, 0 < P i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, ‖β i I‖ ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, β i I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ b i*P i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      (∑ z ∈ rows, ‖centeredSlotRow (childCharacter η χ) m (movingElement p c d V) z
        W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*
        (C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*Ms i)*(Real.sqrt (T*∏ i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩ := exceptional_slots_estimate (ι := κ) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ p hp hinj c d V η χ m e hm hmLam hm2 he rows hrows hex hcond hgood
    Cr Mrow hCr hN S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  refine forcing_finite_energy p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z Cr Mrow _ hZ hCr ?_ hN _ ?_
  · have hprod : 0 ≤ ∏ i,128*b i*Ms i :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hMs i))
    positivity
  · intro z hz
    exact hbound Z hZ.le (childCharacter η χ) m (movingElement p c d V) z hm hA (hrows z hz)
      hmLam hm2 (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeExceptionalEnergy

end

end OAI
